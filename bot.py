from __future__ import annotations

import asyncio
import json
import logging
import os
import re
import sqlite3
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from threading import Lock
from zoneinfo import ZoneInfo

import gspread
from aiogram import Bot, Dispatcher
from aiogram.enums import ChatMemberStatus, ChatType
from aiogram.exceptions import TelegramAPIError
from aiogram.types import BotCommand, ChatMemberUpdated, Message
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.cron import CronTrigger
from google.oauth2.service_account import Credentials
from gspread.exceptions import APIError, SpreadsheetNotFound

# Первая версия по умолчанию никого не блокирует.
# Баны включаются только настройкой BANS_ENABLED=true.
# Дополнительная защита: без отдельного разрешения баны возможны
# только в супергруппе, в названии которой есть «тест» или «test».

USERNAME_RE = re.compile(r"^[a-z][a-z0-9_]{4,31}$")
TELEGRAM_HEADERS = {
    "telegram",
    "telegram username",
    "telegram ник",
    "ник telegram",
    "телеграм",
    "телеграмм",
}
EMPTY_MARKS = {"-", "—", "–", "нет", "н/д", "n/a", "na", "none", "."}
WEEKDAY_MAP = {
    "mon": "mon",
    "monday": "mon",
    "пн": "mon",
    "понедельник": "mon",
    "tue": "tue",
    "tuesday": "tue",
    "вт": "tue",
    "вторник": "tue",
    "wed": "wed",
    "wednesday": "wed",
    "ср": "wed",
    "среда": "wed",
    "thu": "thu",
    "thursday": "thu",
    "чт": "thu",
    "четверг": "thu",
    "fri": "fri",
    "friday": "fri",
    "пт": "fri",
    "пятница": "fri",
    "sat": "sat",
    "saturday": "sat",
    "сб": "sat",
    "суббота": "sat",
    "sun": "sun",
    "sunday": "sun",
    "вс": "sun",
    "воскресенье": "sun",
}
WEEKDAY_RU = {
    "mon": "понедельник",
    "tue": "вторник",
    "wed": "среда",
    "thu": "четверг",
    "fri": "пятница",
    "sat": "суббота",
    "sun": "воскресенье",
}
SCOPES = ["https://www.googleapis.com/auth/spreadsheets.readonly"]

SETTINGS: "Settings | None" = None
BOT: "Bot | None" = None
BOT_ID = 0
DB: "sqlite3.Connection | None" = None
db_lock = Lock()
check_lock = asyncio.Lock()
dp = Dispatcher()


class ConfigError(Exception):
    pass


@dataclass(repr=False)
class Settings:
    bot_token: str
    spreadsheet_id: str
    google_credentials: dict
    report_chat_id: int
    group_ids: list
    bans_enabled: bool
    allow_non_test: bool
    timezone: str
    tz: ZoneInfo
    check_weekday: str
    check_hour: int
    check_minute: int
    db_path: str
    grace_hours: int
    max_bans_per_run: int
    shrink_ratio: float
    shrink_min_previous: int
    skip_sheets: set
    whitelist: set


@dataclass
class SheetData:
    usernames: set
    ok_sheets: list
    skipped_sheets: list
    invalid_examples: list
    invalid_count: int


@dataclass
class PlannedBan:
    chat_id: int
    user_id: int
    username: str
    full_name: "str | None"


@dataclass
class GroupReport:
    chat_id: int
    title: str
    is_supergroup: bool
    is_test: bool
    access_error: "str | None" = None
    admins: int = 0
    protected: int = 0
    matched_names: list = field(default_factory=list)
    no_username: list = field(default_factory=list)
    grace: list = field(default_factory=list)
    unchecked: list = field(default_factory=list)
    to_ban: list = field(default_factory=list)

    @property
    def known(self) -> int:
        return (
            self.admins
            + self.protected
            + len(self.matched_names)
            + len(self.no_username)
            + len(self.grace)
            + len(self.to_ban)
        )


def env_bool(name: str, default: bool = False) -> bool:
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    value = raw.strip().lower()
    if value in {"1", "true", "yes", "да", "on", "вкл"}:
        return True
    if value in {"0", "false", "no", "нет", "off", "выкл"}:
        return False
    raise ConfigError(f"Настройка {name} должна быть true или false.")


def env_int(name: str, default=None) -> int:
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        if default is None:
            raise ConfigError(f"Не задана настройка {name}.")
        return default
    try:
        return int(raw.strip())
    except ValueError as exc:
        raise ConfigError(f"Настройка {name} должна быть целым числом.") from exc


def env_float(name: str, default: float) -> float:
    raw = os.getenv(name)
    if raw is None or raw.strip() == "":
        return default
    try:
        return float(raw.strip().replace(",", "."))
    except ValueError as exc:
        raise ConfigError(f"Настройка {name} должна быть числом.") from exc


def parse_credentials(raw: str) -> dict:
    text = raw.lstrip("\ufeff").strip()
    if not text.startswith("{"):
        raise ConfigError(
            "GOOGLE_CREDENTIALS_JSON должен быть текстом файла-ключа и начинаться с символа {."
        )
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ConfigError(
            "Текст ключа Google не читается. Вставьте весь файл целиком, без кавычек вокруг него."
        ) from exc
    if not isinstance(data, dict) or "private_key" not in data or "client_email" not in data:
        raise ConfigError("В ключе Google нет client_email или private_key.")
    return data


def parse_group_ids(raw: str) -> list:
    result = []
    for part in raw.replace(";", ",").split(","):
        part = part.strip()
        if not part:
            continue
        try:
            value = int(part)
        except ValueError as exc:
            raise ConfigError("GROUP_IDS должен содержать номера групп через запятую.") from exc
        if value >= 0:
            raise ConfigError("Номер группы должен начинаться с минуса, обычно с -100.")
        result.append(value)
    if not result:
        raise ConfigError("Не задана ни одна группа в GROUP_IDS.")
    return result


def load_timezone(name: str):
    try:
        return name, ZoneInfo(name)
    except Exception:
        logging.warning("Таймзона %s недоступна, использую UTC", name)
        return "UTC", ZoneInfo("UTC")


def load_settings() -> Settings:
    token = os.getenv("BOT_TOKEN", "").strip()
    if not token:
        raise ConfigError("Не задан BOT_TOKEN. Его нужно вставить в настройки Coolify, а не в файлы и не в чат.")
    credentials_raw = os.getenv("GOOGLE_CREDENTIALS_JSON", "")
    if not credentials_raw.strip():
        raise ConfigError("Не задан GOOGLE_CREDENTIALS_JSON. Вставьте в Coolify весь текст файла-ключа.")
    credentials = parse_credentials(credentials_raw)
    timezone_name = os.getenv("TIMEZONE", "Europe/Moscow").strip() or "Europe/Moscow"
    timezone_name, tz = load_timezone(timezone_name)
    weekday_raw = os.getenv("CHECK_WEEKDAY", "mon").strip().lower() or "mon"
    if weekday_raw not in WEEKDAY_MAP:
        raise ConfigError("CHECK_WEEKDAY должен быть, например, mon или понедельник.")
    hour = env_int("CHECK_HOUR", 10)
    minute = env_int("CHECK_MINUTE", 0)
    if not 0 <= hour <= 23 or not 0 <= minute <= 59:
        raise ConfigError("CHECK_HOUR должен быть от 0 до 23, CHECK_MINUTE — от 0 до 59.")
    report_chat_id = env_int("REPORT_CHAT_ID", 791088587)
    if report_chat_id < 0:
        raise ConfigError("REPORT_CHAT_ID — это личный номер, без минуса.")
    skip_raw = os.getenv("SHEETS_SKIP", "")
    skip_sheets = {part.strip().lower() for part in skip_raw.replace(";", ",").split(",") if part.strip()}
    whitelist = set()
    for part in os.getenv("WHITELIST_USERNAMES", "").replace(";", ",").split(","):
        username = normalize_username(part)
        if username:
            whitelist.add(username)
    shrink_ratio = env_float("SHRINK_RATIO", 0.7)
    if not 0 < shrink_ratio < 1:
        raise ConfigError("SHRINK_RATIO должен быть между 0 и 1, например 0.7.")
    return Settings(
        bot_token=token,
        spreadsheet_id=os.getenv("SPREADSHEET_ID", "1XpNFbygNmZwOqjJkTYSAhtu0BnQplMon1RXUKO3grsE").strip(),
        google_credentials=credentials,
        report_chat_id=report_chat_id,
        group_ids=parse_group_ids(os.getenv("GROUP_IDS", "-1004351827165")),
        bans_enabled=env_bool("BANS_ENABLED", False),
        allow_non_test=env_bool("ALLOW_NON_TEST", False),
        timezone=timezone_name,
        tz=tz,
        check_weekday=WEEKDAY_MAP[weekday_raw],
        check_hour=hour,
        check_minute=minute,
        db_path=os.getenv("DB_PATH", "/data/bot.db").strip() or "/data/bot.db",
        grace_hours=max(0, env_int("GRACE_HOURS", 24)),
        max_bans_per_run=max(1, env_int("MAX_BANS_PER_RUN", 30)),
        shrink_ratio=shrink_ratio,
        shrink_min_previous=max(1, env_int("SHRINK_MIN_PREVIOUS", 30)),
        skip_sheets=skip_sheets,
        whitelist=whitelist,
    )


def require_settings() -> Settings:
    if SETTINGS is None:
        raise RuntimeError("Настройки ещё не загружены.")
    return SETTINGS


def require_bot() -> Bot:
    if BOT is None:
        raise RuntimeError("Бот ещё не запущен.")
    return BOT


def normalize_username(raw):
    if not raw:
        return None
    value = raw.replace("\u200b", "").replace("\xa0", " ").strip()
    if not value:
        return None
    lower = value.lower()
    for prefix in ("https://", "http://"):
        if lower.startswith(prefix):
            value = value[len(prefix):]
            lower = value.lower()
            break
    for prefix in ("www.t.me/", "www.telegram.me/", "t.me/", "telegram.me/"):
        if lower.startswith(prefix):
            value = value[len(prefix):]
            break
    value = value.split("?", 1)[0].split("/", 1)[0].strip()
    if value.startswith("@"):
        value = value[1:]
    value = value.strip().lower()
    if USERNAME_RE.fullmatch(value):
        return value
    return None


def full_name(user):
    parts = [user.first_name or "", user.last_name or ""]
    name = " ".join(part for part in parts if part).strip()
    return name or None


def format_user(username, user_id: int, name) -> str:
    nick = f"@{username}" if username else "без ника"
    if name:
        return f"{nick}, {name}, id {user_id}"
    return f"{nick}, id {user_id}"


def is_active(member) -> bool:
    status = member.status
    if status in {
        ChatMemberStatus.MEMBER,
        ChatMemberStatus.ADMINISTRATOR,
        ChatMemberStatus.CREATOR,
    }:
        return True
    if status == ChatMemberStatus.RESTRICTED:
        return bool(getattr(member, "is_member", False))
    return False


def is_admin_status(member) -> bool:
    return member.status in {ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.CREATOR}


def is_test_title(title) -> bool:
    value = (title or "").lower()
    return "тест" in value or "test" in value


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def in_grace(joined_at, hours: int) -> bool:
    if not joined_at or hours <= 0:
        return False
    try:
        moment = datetime.fromisoformat(joined_at)
    except ValueError:
        return False
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return datetime.now(timezone.utc) - moment < timedelta(hours=hours)


def local_now_text() -> str:
    settings = require_settings()
    return datetime.now(settings.tz).strftime("%d.%m.%Y %H:%M")


def safe_err(exc: Exception) -> str:
    text = f"{type(exc).__name__}: {exc}"
    secret_marks = ("PRIVATE KEY", "private_key", "BEGIN PRIVATE", "BOT_TOKEN")
    if any(mark in text for mark in secret_marks):
        return type(exc).__name__
    return text[:500]


def init_db(path: str) -> None:
    global DB
    folder = os.path.dirname(path)
    if folder:
        os.makedirs(folder, exist_ok=True)
    connection = sqlite3.connect(path, check_same_thread=False)
    connection.row_factory = sqlite3.Row
    with db_lock:
        connection.execute("PRAGMA journal_mode=WAL")
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS members (
                chat_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                username TEXT,
                full_name TEXT,
                is_member INTEGER NOT NULL,
                is_admin INTEGER NOT NULL,
                first_seen TEXT NOT NULL,
                joined_at TEXT,
                updated_at TEXT NOT NULL,
                PRIMARY KEY (chat_id, user_id)
            )
            """
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
            """
        )
        connection.commit()
    DB = connection


def require_db() -> sqlite3.Connection:
    if DB is None:
        raise RuntimeError("База ещё не открыта.")
    return DB


def meta_get(key: str):
    with db_lock:
        row = require_db().execute("SELECT value FROM meta WHERE key = ?", (key,)).fetchone()
    if row is None:
        return None
    return str(row[0])


def meta_set(key: str, value: str) -> None:
    with db_lock:
        require_db().execute(
            """
            INSERT INTO meta(key, value) VALUES(?, ?)
            ON CONFLICT(key) DO UPDATE SET value = excluded.value
            """,
            (key, value),
        )
        require_db().commit()


def remember(chat_id: int, user, is_member: bool, is_admin, joined_now: bool) -> None:
    if user is None or user.is_bot or user.id == BOT_ID:
        return
    username = (user.username or "").strip().lstrip("@").lower() or None
    name = full_name(user)
    moment = now_iso()
    with db_lock:
        row = require_db().execute(
            "SELECT is_admin, joined_at FROM members WHERE chat_id = ? AND user_id = ?",
            (chat_id, user.id),
        ).fetchone()
        if row is None:
            require_db().execute(
                """
                INSERT INTO members (
                    chat_id, user_id, username, full_name, is_member, is_admin,
                    first_seen, joined_at, updated_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    chat_id,
                    user.id,
                    username,
                    name,
                    1 if is_member else 0,
                    1 if is_admin else 0,
                    moment,
                    moment if joined_now else None,
                    moment,
                ),
            )
            logging.info("Запомнила участника chat=%s user=%s", chat_id, user.id)
        else:
            admin_value = row["is_admin"] if is_admin is None else int(is_admin)
            joined_at = moment if joined_now else row["joined_at"]
            require_db().execute(
                """
                UPDATE members
                   SET username = ?, full_name = ?, is_member = ?, is_admin = ?,
                       joined_at = ?, updated_at = ?
                 WHERE chat_id = ? AND user_id = ?
                """,
                (
                    username,
                    name,
                    1 if is_member else 0,
                    admin_value,
                    joined_at,
                    moment,
                    chat_id,
                    user.id,
                ),
            )
        require_db().commit()


def set_member_state(
    chat_id: int,
    user_id: int,
    username,
    name,
    is_member: bool,
    is_admin: bool,
) -> None:
    with db_lock:
        require_db().execute(
            """
            UPDATE members
               SET username = ?, full_name = ?, is_member = ?, is_admin = ?, updated_at = ?
             WHERE chat_id = ? AND user_id = ?
            """,
            (username, name, int(is_member), int(is_admin), now_iso(), chat_id, user_id),
        )
        require_db().commit()


def get_members(chat_id: int) -> list:
    with db_lock:
        rows = require_db().execute(
            """
            SELECT user_id, username, full_name, is_member, is_admin, joined_at
              FROM members
             WHERE chat_id = ?
             ORDER BY is_member DESC, username COLLATE NOCASE
            """,
            (chat_id,),
        ).fetchall()
    return list(rows)


def find_telegram_column(rows: list):
    for row_index, row in enumerate(rows[:50]):
        for column_index, cell in enumerate(row):
            if cell.strip().lower() in TELEGRAM_HEADERS:
                return row_index, column_index
    return None


def read_spreadsheet(settings: Settings) -> SheetData:
    credentials = Credentials.from_service_account_info(settings.google_credentials, scopes=SCOPES)
    client = gspread.authorize(credentials)
    book = client.open_by_key(settings.spreadsheet_id)
    usernames = set()
    ok_sheets = []
    skipped = []
    invalid_examples = []
    invalid_count = 0
    for sheet in book.worksheets():
        title = sheet.title
        if title.strip().lower() in settings.skip_sheets:
            skipped.append(f"{title} (исключён в настройке)")
            continue
        rows = sheet.get_all_values()
        found = find_telegram_column(rows)
        if found is None:
            skipped.append(f"{title} (нет столбца Telegram)")
            continue
        header_row, column = found
        sheet_count = 0
        for index in range(header_row + 1, len(rows)):
            row = rows[index]
            cell = row[column].strip() if column < len(row) else ""
            if not cell or cell.lower() in EMPTY_MARKS:
                continue
            username = normalize_username(cell)
            if username:
                sheet_count += 1
                usernames.add(username)
                continue
            invalid_count += 1
            if len(invalid_examples) < 20:
                shown = " ".join(cell.split())[:80]
                invalid_examples.append(f"лист «{title}», строка {index + 1}: {shown}")
        ok_sheets.append((title, sheet_count))
    return SheetData(usernames, ok_sheets, skipped, invalid_examples, invalid_count)


def assess_sheet_safety(count: int, has_telegram_sheet: bool):
    settings = require_settings()
    if not has_telegram_sheet or count == 0:
        return False, "Список ников пустой. Это похоже на ошибку чтения, поэтому блокировать нельзя."
    previous = meta_get("last_good_username_count")
    if previous is None:
        return True, ""
    previous_count = int(previous)
    if previous_count >= settings.shrink_min_previous and count < previous_count * settings.shrink_ratio:
        return False, (
            f"В таблице {count} ников, а в прошлый успешный раз было {previous_count}. "
            "Список резко уменьшился, поэтому блокировать нельзя."
        )
    return True, ""


def chunks(text: str, limit: int = 3500) -> list:
    parts = []
    current = []
    size = 0
    for line in text.split("\n"):
        extra = len(line) + 1
        if current and size + extra > limit:
            parts.append("\n".join(current))
            current = [line]
            size = extra
        else:
            current.append(line)
            size += extra
    if current:
        parts.append("\n".join(current))
    return parts


async def send_text(chat_id: int, text: str) -> None:
    text = text.strip()
    if not text:
        return
    bot = require_bot()
    for part in chunks(text):
        try:
            await bot.send_message(chat_id, part)
        except TelegramAPIError as exc:
            logging.error("Не смогла отправить сообщение в %s: %s", chat_id, safe_err(exc))
            if "forbidden" in str(exc).lower() or "chat not found" in str(exc).lower():
                logging.error("Откройте бота в личке и нажмите Start.")
            return
        await asyncio.sleep(0.2)


def add_list(lines: list, title: str, items: list, limit: int = 30) -> None:
    if not items:
        return
    lines.append(title)
    for item in items[:limit]:
        lines.append(f"— {item}")
    if len(items) > limit:
        lines.append(f"— и ещё {len(items) - limit}")


async def inspect_group(group_id: int, allowed: set) -> GroupReport:
    settings = require_settings()
    bot = require_bot()
    try:
        chat = await bot.get_chat(group_id)
    except TelegramAPIError as exc:
        return GroupReport(
            chat_id=group_id,
            title=str(group_id),
            is_supergroup=False,
            is_test=False,
            access_error=f"Не могу открыть группу. Бот должен быть в ней администратором. {safe_err(exc)}",
        )
    report = GroupReport(
        chat_id=group_id,
        title=chat.title or str(group_id),
        is_supergroup=chat.type == ChatType.SUPERGROUP,
        is_test=is_test_title(chat.title),
    )
    for row in get_members(group_id):
        if not row["is_member"]:
            continue
        label = format_user(row["username"], row["user_id"], row["full_name"])
        try:
            live = await bot.get_chat_member(group_id, row["user_id"])
        except TelegramAPIError as exc:
            report.unchecked.append(f"{label}: {safe_err(exc)}")
            continue
        user = live.user
        username = (user.username or "").lower() or None
        name = full_name(user)
        active = is_active(live)
        admin = is_admin_status(live)
        set_member_state(
            group_id,
            user.id,
            username=username,
            name=name,
            is_member=active,
            is_admin=admin,
        )
        if not active or user.is_bot:
            continue
        if admin:
            report.admins += 1
            continue
        if user.id in {settings.report_chat_id, BOT_ID}:
            report.protected += 1
            continue
        if not username:
            report.no_username.append(format_user(None, user.id, name))
            continue
        if username in settings.whitelist:
            report.protected += 1
            continue
        pretty = format_user(username, user.id, name)
        if username in allowed:
            report.matched_names.append(pretty)
            continue
        if in_grace(row["joined_at"], settings.grace_hours):
            report.grace.append(pretty)
            continue
        report.to_ban.append(PlannedBan(group_id, user.id, username, name))
        await asyncio.sleep(0.03)
    return report


async def execute_bans(bans: list):
    settings = require_settings()
    bot = require_bot()
    if not settings.bans_enabled:
        return [], [], len(bans)
    done = []
    failed = []
    batch = bans[: settings.max_bans_per_run]
    for item in batch:
        label = format_user(item.username, item.user_id, item.full_name)
        try:
            fresh = await bot.get_chat_member(item.chat_id, item.user_id)
        except TelegramAPIError as exc:
            failed.append(f"{label}: не удалось перепроверить ({safe_err(exc)})")
            continue
        current_username = (fresh.user.username or "").lower()
        if (
            not is_active(fresh)
            or is_admin_status(fresh)
            or fresh.user.is_bot
            or fresh.user.id in {settings.report_chat_id, BOT_ID}
            or current_username != item.username
        ):
            failed.append(f"{label}: перед блокировкой статус изменился, пропустила")
            continue
        try:
            await bot.ban_chat_member(item.chat_id, item.user_id, revoke_messages=False)
        except TelegramAPIError as exc:
            failed.append(f"{label}: {safe_err(exc)}")
            continue
        set_member_state(
            item.chat_id,
            item.user_id,
            username=current_username,
            name=item.full_name,
            is_member=False,
            is_admin=False,
        )
        done.append(label)
        logging.info("Заблокирован user=%s chat=%s", item.user_id, item.chat_id)
        await asyncio.sleep(0.5)
    left = max(0, len(bans) - len(batch))
    return done, failed, left


def group_lines(group: GroupReport) -> list:
    lines = ["", f"Группа «{group.title}»", f"Номер: {group.chat_id}"]
    if group.access_error:
        lines.append(group.access_error)
        return lines
    if not group.is_supergroup:
        lines.append("Это не супергруппа. Блокировки здесь не будет.")
    if not group.is_test and not require_settings().allow_non_test:
        lines.append("В названии нет слова «тест». Блокировки здесь не будет.")
    lines.append(f"Сейчас видит в чате: {group.known}")
    lines.append(f"Администраторы, их не трогаю: {group.admins}")
    if group.protected:
        lines.append(f"Дополнительно защищены от блокировки: {group.protected}")
    if len(group.matched_names) <= 15:
        add_list(lines, f"Есть в таблице: {len(group.matched_names)}", group.matched_names)
    else:
        lines.append(f"Есть в таблице: {len(group.matched_names)}")
    add_list(lines, "Без ника, их не трогаю:", group.no_username)
    add_list(lines, "Вступили недавно, их не трогаю:", group.grace)
    add_list(lines, "Не удалось перепроверить, их не трогаю:", group.unchecked)
    if group.known == 0 and not group.unchecked:
        lines.append(
            "Бот ещё никого не запомнил. Напишите в этой группе обычное сообщение "
            "со своего аккаунта. Бот в группе отвечать не будет. Затем напишите мне: проверка"
        )
    return lines


async def do_check(reason: str) -> None:
    settings = require_settings()
    lines = [f"Проверка {local_now_text()} ({reason})"]
    if settings.bans_enabled:
        lines.append("Баны включены в настройке.")
    else:
        lines.append("Баны выключены. Это только отчёт, никого не блокирую.")
    if not settings.allow_non_test:
        lines.append("Рабочий чат компании не подключён. Для блокировки название группы должно содержать «тест».")
    lines.append("")
    try:
        data = read_spreadsheet(settings)
    except SpreadsheetNotFound:
        await send_text(
            settings.report_chat_id,
            "\n".join(lines) + "\n\nТаблица по этому номеру не найдена. Никого не блокирую.",
        )
        return
    except APIError as exc:
        text = str(exc).lower()
        if "403" in text or "permission" in text:
            details = "Нет доступа к таблице. Адрес sheets-reader должен быть читателем."
        else:
            details = safe_err(exc)
        await send_text(
            settings.report_chat_id,
            "\n".join(lines) + f"\n\nТаблица не открылась. Никого не блокирую.\n{details}",
        )
        return
    safe, safety_text = assess_sheet_safety(len(data.usernames), bool(data.ok_sheets))
    lines.append(f"В таблице уникальных ников: {len(data.usernames)}")
    lines.append("Числа по листам могут повторять одного человека. В общем числе он один.")
    lines.append("Листы:")
    if data.ok_sheets:
        for title, count in data.ok_sheets:
            lines.append(f"— {title}: {count}")
    else:
        lines.append("— нет листа со столбцом Telegram")
    if data.skipped_sheets:
        lines.append("Пропущены:")
        for title in data.skipped_sheets:
            lines.append(f"— {title}")
    lines.append(f"Ячеек, которые не похожи на ник: {data.invalid_count}")
    add_list(lines, "Примеры таких ячеек:", data.invalid_examples, 20)
    lines.append("Почты и фамилии не сохраняю и в отчёт не беру.")
    if safety_text:
        lines.append(safety_text)
    if settings.whitelist:
        whitelist = ", ".join(f"@{item}" for item in sorted(settings.whitelist))
        lines.append(f"Исключения: {whitelist}")

    groups = []
    for group_id in settings.group_ids:
        groups.append(await inspect_group(group_id, data.usernames))
        lines.extend(group_lines(groups[-1]))

    eligible = []
    for group in groups:
        lines.append("")
        if group.to_ban:
            names = [format_user(item.username, item.user_id, item.full_name) for item in group.to_ban]
            title = "Попали бы под блокировку:" if not settings.bans_enabled else "Нет в таблице:"
            add_list(lines, title, names, 100)
        else:
            lines.append(f"В «{group.title}» среди тех, кого бот видит, лишних нет.")
        group_allowed = (
            group.access_error is None
            and group.is_supergroup
            and (group.is_test or settings.allow_non_test)
        )
        if group_allowed:
            eligible.extend(group.to_ban)

    lines.append("")
    if not settings.bans_enabled:
        lines.append("Блокировка не выполнялась: баны выключены.")
    elif not safe:
        lines.append("Блокировка не выполнялась из-за защиты таблицы.")
    elif not eligible:
        lines.append("Блокировать некого.")
    else:
        done, failed, left = await execute_bans(eligible)
        add_list(lines, f"Заблокированы: {len(done)}", done, 50)
        add_list(lines, f"Не удалось заблокировать: {len(failed)}", failed, 50)
        if left:
            lines.append(f"Из-за ограничения ещё {left} человек оставлены на следующий запуск.")
    if safe:
        meta_set("last_good_username_count", str(len(data.usernames)))
    weekday = WEEKDAY_RU[settings.check_weekday]
    lines.append(
        f"Следующая автопроверка: {weekday}, {settings.check_hour:02d}:{settings.check_minute:02d} ({settings.timezone})."
    )
    lines.append("Раньше можно написать мне слово: проверка")
    logging.info(
        "Проверка завершена: ников=%s кандидатов=%s баны=%s",
        len(data.usernames),
        len(eligible),
        settings.bans_enabled,
    )
    await send_text(settings.report_chat_id, "\n".join(lines))


async def run_check(reason: str) -> None:
    if check_lock.locked():
        logging.info("Проверка уже идёт, пропуск: %s", reason)
        if reason == "по запросу":
            await send_text(
                require_settings().report_chat_id,
                "Проверка уже идёт. Подождите минуту и напишите ещё раз.",
            )
        return
    async with check_lock:
        try:
            await do_check(reason)
        except Exception as exc:
            logging.exception("Проверка сломалась")
            await send_text(
                require_settings().report_chat_id,
                "Проверка не выполнилась. Никого не блокирую.\n" + safe_err(exc),
            )


def command_name(text: str) -> str:
    value = text.strip().lower()
    if value.startswith("/"):
        value = value[1:].split()[0].split("@")[0]
    aliases = {
        "start": "help",
        "help": "help",
        "помощь": "help",
        "report": "check",
        "check": "check",
        "проверка": "check",
        "проверить": "check",
        "отчет": "check",
        "отчёт": "check",
        "members": "members",
        "участники": "members",
        "база": "members",
        "status": "status",
        "статус": "status",
        "баны": "status",
    }
    return aliases.get(value, value)


async def send_help() -> None:
    settings = require_settings()
    mode = "включены" if settings.bans_enabled else "выключены"
    await send_text(
        settings.report_chat_id,
        "\n".join(
            [
                f"Баны сейчас {mode}.",
                "В группе бот молчит. Отчёт приходит только сюда.",
                "",
                "Напишите одно слово:",
                "проверка — прочитать таблицу и показать, кого бот видит",
                "участники — список тех, кого бот уже запомнил",
                "статус — включены ли баны и какие группы подключены",
            ]
        ),
    )


async def send_status() -> None:
    settings = require_settings()
    groups = ", ".join(str(group_id) for group_id in settings.group_ids)
    weekday = WEEKDAY_RU[settings.check_weekday]
    lines = [
        "Баны: ВКЛЮЧЕНЫ." if settings.bans_enabled else "Баны: выключены.",
        f"Группы: {groups}",
        f"Отчёты приходят сюда: {settings.report_chat_id}",
        f"Автопроверка: {weekday}, {settings.check_hour:02d}:{settings.check_minute:02d} ({settings.timezone}).",
        "Можно проверять группы без слова «тест»."
        if settings.allow_non_test
        else "Группу без слова «тест» в названии бот не заблокирует.",
    ]
    await send_text(settings.report_chat_id, "\n".join(lines))


async def send_members() -> None:
    settings = require_settings()
    lines = ["Кого бот запомнил:"]
    total = 0
    for group_id in settings.group_ids:
        rows = get_members(group_id)
        total += len(rows)
        lines.append("")
        lines.append(f"Группа {group_id}: {len(rows)}")
        for row in rows[:80]:
            state = "в чате" if row["is_member"] else "уже не в чате"
            if row["is_admin"]:
                state += ", администратор"
            lines.append("— " + format_user(row["username"], row["user_id"], row["full_name"]) + f" ({state})")
        if len(rows) > 80:
            lines.append(f"— и ещё {len(rows) - 80}")
    if total == 0:
        lines.append("")
        lines.append("Пока пусто. Напишите обычное сообщение в тестовой группе, затем снова: участники")
    await send_text(settings.report_chat_id, "\n".join(lines))


async def handle_private(message: Message) -> None:
    settings = require_settings()
    if message.from_user is None:
        return
    if message.from_user.id != settings.report_chat_id:
        await message.answer("Этот бот отвечает только администратору.")
        return
    if not message.text:
        await message.answer("Напишите слово: проверка")
        return
    name = command_name(message.text)
    if name == "help":
        await send_help()
    elif name == "check":
        await run_check("по запросу")
    elif name == "members":
        await send_members()
    elif name == "status":
        await send_status()
    else:
        await send_help()


def handle_group_message(message: Message) -> None:
    settings = require_settings()
    if message.chat.id not in settings.group_ids:
        return
    if message.left_chat_member is not None:
        remember(
            message.chat.id,
            message.left_chat_member,
            is_member=False,
            is_admin=None,
            joined_now=False,
        )
        return
    if message.new_chat_members:
        for user in message.new_chat_members:
            remember(message.chat.id, user, is_member=True, is_admin=False, joined_now=True)
    if message.from_user is not None:
        remember(
            message.chat.id,
            message.from_user,
            is_member=True,
            is_admin=None,
            joined_now=False,
        )


@dp.message()
async def on_message(message: Message) -> None:
    try:
        if message.chat.type == ChatType.PRIVATE:
            await handle_private(message)
        elif message.chat.type in {ChatType.GROUP, ChatType.SUPERGROUP}:
            handle_group_message(message)
    except Exception:
        logging.exception("Ошибка обработки сообщения")


@dp.chat_member()
async def on_chat_member(event: ChatMemberUpdated) -> None:
    try:
        settings = require_settings()
        if event.chat.id not in settings.group_ids:
            return
        member = event.new_chat_member
        if member.user.is_bot:
            return
        joined_now = is_active(member) and not is_active(event.old_chat_member)
        remember(
            event.chat.id,
            member.user,
            is_member=is_active(member),
            is_admin=is_admin_status(member),
            joined_now=joined_now,
        )
    except Exception:
        logging.exception("Ошибка события участника")


@dp.my_chat_member()
async def on_my_chat_member(event: ChatMemberUpdated) -> None:
    try:
        settings = require_settings()
        title = event.chat.title or "без названия"
        status = event.new_chat_member.status
        if event.chat.id in settings.group_ids:
            text = f"Статус бота в подключённой группе «{title}» ({event.chat.id}): {status}."
        elif event.chat.type in {ChatType.GROUP, ChatType.SUPERGROUP}:
            text = (
                f"Бота добавили в группу «{title}».\n"
                f"Её номер: {event.chat.id}.\n"
                "Эта группа пока не подключена: бот её не проверяет и никого там не блокирует.\n"
                "Если это рабочий чат компании, удалите оттуда бота до конца теста."
            )
        else:
            return
        await send_text(settings.report_chat_id, text)
    except Exception:
        logging.exception("Ошибка статуса бота")


def startup_text(username) -> str:
    name = f"@{username}" if username else "Бот"
    return "\n".join(
        [
            f"{name} запущен.",
            "Баны выключены: никого не блокирую, только присылаю отчёт.",
            "Рабочий чат компании не подключён.",
            "",
            "Сейчас пришлю первую проверку.",
            "Потом можно писать сюда словами:",
            "проверка — сверить таблицу",
            "участники — кого бот уже видел",
            "статус — включены ли баны",
        ]
    )


async def scheduled_check() -> None:
    logging.info("Запущена проверка по расписанию")
    await run_check("по расписанию")


async def amain() -> None:
    global SETTINGS, BOT, BOT_ID
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    logging.getLogger("google").setLevel(logging.WARNING)
    logging.getLogger("urllib3").setLevel(logging.WARNING)
    SETTINGS = load_settings()
    init_db(SETTINGS.db_path)
    BOT = Bot(SETTINGS.bot_token)
    try:
        me = await BOT.get_me()
    except Exception as exc:
        logging.error("Токен бота не подошёл: %s", safe_err(exc))
        raise SystemExit(1) from exc
    BOT_ID = me.id
    logging.info("Бот @%s, id %s", me.username, me.id)
    logging.info(
        "Группы %s, отчёты %s, баны %s, Google %s",
        SETTINGS.group_ids,
        SETTINGS.report_chat_id,
        SETTINGS.bans_enabled,
        SETTINGS.google_credentials.get("client_email", ""),
    )
    scheduler = AsyncIOScheduler(timezone=SETTINGS.tz)
    scheduler.add_job(
        scheduled_check,
        CronTrigger(
            day_of_week=SETTINGS.check_weekday,
            hour=SETTINGS.check_hour,
            minute=SETTINGS.check_minute,
        ),
        id="weekly_check",
        replace_existing=True,
        max_instances=1,
        coalesce=True,
    )
    scheduler.start()
    try:
        await BOT.set_my_commands(
            [
                BotCommand(command="report", description="Проверить таблицу"),
                BotCommand(command="members", description="Кого бот уже видел"),
                BotCommand(command="status", description="Включены ли баны"),
            ]
        )
        await send_text(SETTINGS.report_chat_id, startup_text(me.username))
        await run_check("при запуске")
        await dp.start_polling(
            BOT,
            allowed_updates=["message", "chat_member", "my_chat_member"],
        )
    finally:
        scheduler.shutdown(wait=False)
        await BOT.session.close()


def main() -> None:
    try:
        asyncio.run(amain())
    except ConfigError as exc:
        logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
        logging.error("%s", exc)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
