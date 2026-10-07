"""Барбершоп: Telegram-бот + сайт із записом + нагадування. Одна програма, одна база.

- Запис у боті й на сайті потрапляє в одну базу (SQLite), тому зайнятий час зникає в обох місцях.
- Нагадування: у день візиту (09:00) і приблизно за 4 години до запису (Telegram + SMS, якщо увімкнено).
- Клієнт із сайту може натиснути «Підключити нагадування в Telegram», і нагадування прийдуть у чат.
- Сайт (папка web/) віддається цією ж програмою, API: /api/config, /api/days, /api/slots, /api/book.
"""
import asyncio
import csv
import io
import logging
import os
import re
import secrets
import sqlite3
import time as _time
from contextlib import closing
from datetime import date, datetime, time, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import aiohttp
from aiogram import Bot, Dispatcher, F, Router
from aiogram.exceptions import TelegramBadRequest
from aiogram.filters import Command, CommandObject, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BotCommand,
    BotCommandScopeChat,
    CallbackQuery,
    InlineKeyboardButton,
    KeyboardButton,
    MenuButtonWebApp,
    Message,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    WebAppInfo,
)
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiohttp import web
from dotenv import load_dotenv

load_dotenv()

# ---------- Налаштування (з файлу .env) ----------
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")
ADMIN_IDS = [int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").split(",") if x]
TZ = ZoneInfo(os.getenv("TZ_NAME", "Europe/Kyiv"))
SHOP_NAME = os.getenv("SHOP_NAME", "Барбершоп «Борода»")
ADDRESS = os.getenv("SHOP_ADDRESS", "вул. Прикладна, 1")
MORNING_HOUR = int(os.getenv("MORNING_HOUR", "9"))
DB_PATH = os.getenv("DB_PATH", "barber.db")  # на хостингу вкажіть шлях на постійному томі, напр. /data/barber.db

WEB_HOST = os.getenv("WEB_HOST", "0.0.0.0")
WEB_PORT = int(os.getenv("PORT", "8080"))
ALLOWED_ORIGIN = os.getenv("ALLOWED_ORIGIN", "")  # потрібно лише якщо сайт лежить на іншому домені
BOT_USERNAME = os.getenv("BOT_USERNAME", "")  # якщо порожньо, візьметься автоматично
WEB_DIR = Path(__file__).parent / "web"

SMS_ENABLED = os.getenv("SMS_ENABLED", "0") == "1"
TURBOSMS_TOKEN = os.getenv("TURBOSMS_TOKEN", "")
TURBOSMS_SENDER = os.getenv("TURBOSMS_SENDER", "")

PUBLIC_URL = os.getenv("PUBLIC_URL", "")  # https-адреса сайту: у боті з'явиться кнопка «Сайт»
REMIND_HOURS = int(os.getenv("REMIND_HOURS", "4"))  # за скільки годин нагадувати про запис
REMIND_NOT_BEFORE = int(os.getenv("REMIND_NOT_BEFORE", "7"))  # не будити клієнтів раніше цієї години
LOYALTY_EVERY = int(os.getenv("LOYALTY_EVERY", "5"))  # кожен N-й запис зі знижкою (0 = вимкнено)
LOYALTY_PERCENT = int(os.getenv("LOYALTY_PERCENT", "10"))

# ---------- Послуги, майстри, графік ----------
SERVICES = {  # id: (назва, хвилин, ціна грн)
    "cut": ("Стрижка", 45, 400),
    "beard": ("Борода", 30, 250),
    "combo": ("Стрижка + борода", 75, 600),
    "kid": ("Дитяча стрижка", 30, 300),
}
MASTERS = {"a": "Андрій", "m": "Максим", "o": "Олег"}
VALID_MASTERS = set(MASTERS) | {"any"}  # "any" = будь-який вільний майстер
ANY_NAME = "Будь-який вільний"
OPEN_HOUR = 10  # перший слот о 10:00
SLOTS = 18  # 18 слотів по 30 хв: останній починається о 18:30, закриття о 19:00
BOOK_DAYS = 7  # на скільки днів уперед можна записатися
MAX_ACTIVE_PER_PHONE = 3  # скільки майбутніх записів може мати один номер
WEEKDAYS = ["пн", "вт", "ср", "чт", "пт", "сб", "нд"]

router = Router()
LOCK = asyncio.Lock()


class Booking(StatesGroup):
    phone = State()


class BookingError(Exception):
    """Помилка запису з текстом, який можна показати клієнту."""


# ---------- База даних ----------
SCHEMA = """
CREATE TABLE IF NOT EXISTS appts(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    tg_id INTEGER,
    name TEXT,
    phone TEXT,
    service TEXT,
    master TEXT,
    start TEXT,
    status TEXT DEFAULT 'booked',
    source TEXT DEFAULT 'bot',
    token TEXT,
    price INTEGER,
    note TEXT
);
CREATE TABLE IF NOT EXISTS reminders(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    appt_id INTEGER,
    kind TEXT,
    send_at TEXT,
    sent INTEGER DEFAULT 0
);
CREATE TABLE IF NOT EXISTS auth_tokens(token TEXT PRIMARY KEY, tg_id INTEGER, name TEXT, created TEXT);
CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY, tg_id INTEGER, name TEXT, created TEXT);
CREATE TABLE IF NOT EXISTS reviews(id INTEGER PRIMARY KEY AUTOINCREMENT, appt_id INTEGER, tg_id INTEGER, rating INTEGER, created TEXT);
"""


def db() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db() -> None:
    with closing(db()) as c:
        cols = c.execute("PRAGMA table_info(appts)").fetchall()
        old = bool(cols) and (
            any(r["name"] == "tg_id" and r["notnull"] for r in cols) or "token" not in {r["name"] for r in cols}
        )
        if old:  # міграція зі старої версії бази
            c.executescript("ALTER TABLE appts RENAME TO appts_old;")
        c.executescript(SCHEMA)
        if old:
            c.execute(
                "INSERT INTO appts(id,tg_id,name,phone,service,master,start,status) "
                "SELECT id,tg_id,name,phone,service,master,start,status FROM appts_old"
            )
            c.execute("DROP TABLE appts_old")
        have = {r["name"] for r in c.execute("PRAGMA table_info(appts)")}
        for col, typ in (("price", "INTEGER"), ("note", "TEXT")):
            if col not in have:
                c.execute(f"ALTER TABLE appts ADD COLUMN {col} {typ}")
        c.commit()
        backfill_reminders(c)


def backfill_reminders(c) -> None:
    """Майбутнім записам без нагадування (старі записи) створює нагадування."""
    n = now()
    rows = c.execute("SELECT id, start FROM appts WHERE status='booked' AND start>?", (n.isoformat(timespec="seconds"),)).fetchall()
    for a in rows:
        if c.execute("SELECT 1 FROM reminders WHERE appt_id=? AND kind='4h'", (a["id"],)).fetchone():
            continue
        for kind, when in plan_reminders(datetime.fromisoformat(a["start"]), n):
            c.execute("INSERT INTO reminders(appt_id, kind, send_at) VALUES(?,?,?)", (a["id"], kind, when.isoformat(timespec="seconds")))
    c.commit()


# ---------- Допоміжні функції ----------
def now() -> datetime:
    return datetime.now(TZ).replace(tzinfo=None)


def units(service: str) -> int:
    return -(-SERVICES[service][1] // 30)


def slot_label(i: int) -> str:
    m = OPEN_HOUR * 60 + 30 * i
    return f"{m // 60:02d}:{m % 60:02d}"


def slot_dt(day: date, i: int) -> datetime:
    return datetime.combine(day, time(OPEN_HOUR)) + timedelta(minutes=30 * i)


def fmt(dt: datetime) -> str:
    return f"{dt:%d.%m.%Y} о {dt:%H:%M}"


def master_name(mid: str) -> str:
    return MASTERS.get(mid, ANY_NAME)


def normalize_phone(raw: str):
    digits = re.sub(r"\D", "", raw or "")
    if len(digits) == 10 and digits.startswith("0"):
        digits = "38" + digits
    if len(digits) == 12 and digits.startswith("380"):
        return "+" + digits
    return None


def busy_slots(day: date, master: str, skip_id: int = 0) -> set:
    """Зайняті слоти майстра. Завершені візити ('done') теж зайняті, щоб час не відкривався повторно."""
    busy = set()
    with closing(db()) as c:
        rows = c.execute(
            "SELECT service, start FROM appts "
            "WHERE master=? AND status IN ('booked','done') AND id<>? AND substr(start,1,10)=?",
            (master, skip_id, day.isoformat()),
        ).fetchall()
    for r in rows:
        if r["service"] not in SERVICES:
            continue
        st = datetime.fromisoformat(r["start"])
        i = ((st.hour * 60 + st.minute) - OPEN_HOUR * 60) // 30
        for k in range(units(r["service"])):
            busy.add(i + k)
    return busy


def free_slots(day: date, master: str, service: str, lead: int = 30) -> list:
    if master == "any":  # об'єднання вільних слотів усіх майстрів
        out = set()
        for m in MASTERS:
            out |= set(free_slots(day, m, service, lead))
        return sorted(out)
    busy = busy_slots(day, master)
    u = units(service)
    limit = now() + timedelta(minutes=lead)  # клієнт може записатися не пізніше ніж за 30 хв
    result = []
    for i in range(SLOTS):
        if i + u > SLOTS:
            break
        if any((i + k) in busy for k in range(u)):
            continue
        if slot_dt(day, i) <= limit:
            continue
        result.append(i)
    return result


def plan_reminders(start: datetime, created: datetime) -> list:
    """Нагадування за REMIND_HOURS год до запису. Щоб не будити клієнтів, не раніше
    REMIND_NOT_BEFORE:00 того ж дня. Якщо час уже минув на момент запису, нагадування не створюється."""
    when = max(start - timedelta(hours=REMIND_HOURS), datetime.combine(start.date(), time(REMIND_NOT_BEFORE)))
    return [("4h", when)] if created < when < start else []


# ---------- Єдина функція створення запису (бот, сайт, CRM) ----------
def price_for(c, sid: str, tg_id, phone: str) -> int:
    """Кожен LOYALTY_EVERY-й запис клієнта іде зі знижкою LOYALTY_PERCENT%."""
    base = SERVICES[sid][2]
    if LOYALTY_EVERY > 0:
        n = c.execute(
            "SELECT COUNT(*) FROM appts WHERE status IN ('done','booked') AND (phone=? OR (? IS NOT NULL AND tg_id=?))",
            (phone, tg_id, tg_id),
        ).fetchone()[0]
        if (n + 1) % LOYALTY_EVERY == 0:
            return round(base * (100 - LOYALTY_PERCENT) / 100)
    return base


async def create_appointment(*, name, phone, sid, mid, day, slot, tg_id, source, admin=False, note=""):
    lead = 0 if admin else 30  # адміністратор може записати й на найближчий час
    async with LOCK:  # захист від двох записів на один час
        if mid == "any":  # обираємо першого вільного майстра
            mid = next((m for m in MASTERS if slot in free_slots(day, m, sid, lead)), None)
        if mid is None or slot not in free_slots(day, mid, sid, lead):
            raise BookingError("На жаль, цей час щойно зайняли. Оберіть інший.")
        start = slot_dt(day, slot)
        with closing(db()) as c:
            if not admin:
                active = c.execute(
                    "SELECT COUNT(*) FROM appts WHERE phone=? AND status='booked' AND start>?",
                    (phone, now().isoformat(timespec="seconds")),
                ).fetchone()[0]
                if active >= MAX_ACTIVE_PER_PHONE:
                    raise BookingError("На цей номер уже оформлено кілька записів. Скасуйте зайвий або зателефонуйте нам.")
            price = price_for(c, sid, tg_id, phone)
            cur = c.execute(
                "INSERT INTO appts(tg_id, name, phone, service, master, start, source, token, price, note) VALUES(?,?,?,?,?,?,?,?,?,?)",
                (tg_id, name, phone, sid, mid, start.isoformat(timespec="seconds"), source, secrets.token_urlsafe(8), price, note),
            )
            appt_id = cur.lastrowid
            for kind, when in plan_reminders(start, now()):
                c.execute(
                    "INSERT INTO reminders(appt_id, kind, send_at) VALUES(?,?,?)",
                    (appt_id, kind, when.isoformat(timespec="seconds")),
                )
            c.commit()
            return c.execute("SELECT * FROM appts WHERE id=?", (appt_id,)).fetchone()


# ---------- Тексти ----------
def text_confirm(a) -> str:
    name, mins, base = SERVICES[a["service"]]
    price = a["price"] if a["price"] is not None else base
    disc = f" (знижка лояльності −{LOYALTY_PERCENT}%)" if price < base else ""
    return (
        "✅ Запис підтверджено\n\n"
        f"{SHOP_NAME}\n"
        f"📅 {fmt(datetime.fromisoformat(a['start']))}\n"
        f"✂️ {name}, {mins} хв\n"
        f"👤 Майстер: {master_name(a['master'])}\n"
        f"💰 {price} ₴{disc}\n"
        f"📍 {ADDRESS}\n\n"
        "Ми нагадаємо про візит. Якщо плани змінилися, скасуйте запис: /my"
    )


def text_reminder(kind: str, a) -> str:
    st = datetime.fromisoformat(a["start"])
    name = SERVICES[a["service"]][0]
    head = "⏰ Нагадуємо про ваш запис сьогодні."
    return (
        f"{head}\n\n"
        f"🕒 {st:%H:%M}, {name}\n"
        f"👤 Майстер: {master_name(a['master'])}\n"
        f"📍 {SHOP_NAME}, {ADDRESS}\n\n"
        "Не встигаєте? Скасуйте запис: /my"
    )


def sms_confirm(a) -> str:
    st = datetime.fromisoformat(a["start"])
    return f"{SHOP_NAME}: запис {st:%d.%m} о {st:%H:%M}. {ADDRESS}"


def sms_reminder(a) -> str:
    st = datetime.fromisoformat(a["start"])
    return f"{SHOP_NAME}: нагадуємо, сьогодні о {st:%H:%M} ваш запис. {ADDRESS}"


# ---------- Сповіщення ----------
async def send_sms(phone: str, text: str) -> None:
    """SMS через TurboSMS. Перевірте формат запиту в документації вашого провайдера."""
    if not (SMS_ENABLED and TURBOSMS_TOKEN and TURBOSMS_SENDER):
        return
    payload = {
        "recipients": [phone.lstrip("+")],
        "sms": {"sender": TURBOSMS_SENDER, "text": text},
    }
    headers = {"Authorization": f"Bearer {TURBOSMS_TOKEN}"}
    try:
        async with aiohttp.ClientSession() as s:
            async with s.post(
                "https://api.turbosms.ua/message/send.json",
                json=payload,
                headers=headers,
                timeout=aiohttp.ClientTimeout(total=15),
            ) as r:
                body = await r.text()
                if r.status != 200:
                    logging.error("SMS не надіслано: %s %s", r.status, body)
    except Exception:
        logging.exception("Помилка надсилання SMS")


async def notify_client(bot, a, text: str, sms_text: str, kb=None) -> None:
    if a["tg_id"]:  # записи з сайту без прив'язки до Telegram отримують лише SMS
        try:
            await bot.send_message(a["tg_id"], text, reply_markup=kb)
        except Exception:
            logging.exception("Не вдалося надіслати повідомлення клієнту %s", a["tg_id"])
    await send_sms(a["phone"], sms_text)


async def notify_admins(bot, text: str) -> None:
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(admin_id, text)
        except Exception:
            logging.exception("Не вдалося надіслати повідомлення адміну %s", admin_id)


async def after_booking(bot, a) -> None:
    await notify_client(bot, a, text_confirm(a), sms_confirm(a))
    src = {"web": "сайт", "admin": "CRM"}.get(a["source"], "Telegram-бот")
    start = datetime.fromisoformat(a["start"])
    await notify_admins(
        bot,
        f"🆕 Новий запис ({src})\n{a['name']} · {a['phone']}\n"
        f"{SERVICES[a['service']][0]}, {master_name(a['master'])}\n{fmt(start)}",
    )


# ---------- Клавіатури ----------
def kb_main():
    b = InlineKeyboardBuilder()
    b.button(text="Записатися", callback_data="book")
    b.button(text="Мої записи", callback_data="my")
    b.button(text="Ціни та адреса", callback_data="info")
    b.adjust(1)
    return b.as_markup()


def kb_services():
    b = InlineKeyboardBuilder()
    for sid, (name, _mins, price) in SERVICES.items():
        b.button(text=f"{name} · {price} ₴", callback_data=f"s:{sid}")
    b.button(text="‹ Назад", callback_data="home")
    b.adjust(1)
    return b.as_markup()


def kb_masters(sid: str):
    b = InlineKeyboardBuilder()
    b.button(text=ANY_NAME + " майстер", callback_data=f"m:{sid}:any")
    for mid, name in MASTERS.items():
        b.button(text=name, callback_data=f"m:{sid}:{mid}")
    b.button(text="‹ Назад", callback_data="book")
    b.adjust(1)
    return b.as_markup()


def kb_remind(appt_id: int):
    b = InlineKeyboardBuilder()
    b.button(text="✅ Буду", callback_data=f"ok:{appt_id}")
    b.button(text="❌ Скасувати запис", callback_data=f"x:{appt_id}")
    b.adjust(2)
    return b.as_markup()


def kb_rate(appt_id: int):
    b = InlineKeyboardBuilder()
    for n in range(1, 6):
        b.button(text="⭐" * n if n < 3 else f"{n}⭐", callback_data=f"r:{appt_id}:{n}")
    b.adjust(5)
    return b.as_markup()


async def send_review_request(bot, a) -> None:
    if a["tg_id"]:
        await bot.send_message(
            a["tg_id"], f"Дякуємо за візит у «{SHOP_NAME}»! ✂️\nОцініть, будь ласка, як усе пройшло:", reply_markup=kb_rate(a["id"])
        )


async def show(cb: CallbackQuery, text: str, kb=None) -> None:
    try:
        await cb.message.edit_text(text, reply_markup=kb)
    except TelegramBadRequest:
        pass
    await cb.answer()


# ---------- Команди ----------
@router.message(CommandStart(deep_link=True))
async def cmd_start_link(m: Message, command: CommandObject, state: FSMContext):
    """Посилання з сайту: t.me/бот?start=link_ТОКЕН прив'язує запис до цього чату."""
    payload = command.args or ""
    if payload.startswith("login_"):  # вхід на сайті через Telegram
        cutoff = (now() - timedelta(minutes=10)).isoformat(timespec="seconds")
        with closing(db()) as c:
            row = c.execute("SELECT token FROM auth_tokens WHERE token=? AND created>?", (payload[6:], cutoff)).fetchone()
            if row:
                c.execute("UPDATE auth_tokens SET tg_id=?, name=? WHERE token=?", (m.from_user.id, m.from_user.full_name, row["token"]))
                c.commit()
        await state.clear()
        await m.answer(
            "Ви увійшли на сайт ✅ Поверніться на сторінку, вхід завершиться автоматично."
            if row else "Посилання входу застаріло. Поверніться на сайт і натисніть «Увійти» ще раз.",
            reply_markup=kb_panel(m.from_user.id),
        )
        return
    if payload.startswith("link_"):
        with closing(db()) as c:
            a = c.execute("SELECT * FROM appts WHERE token=? AND status='booked'", (payload[5:],)).fetchone()
            if a and (a["tg_id"] is None or a["tg_id"] == m.from_user.id):
                c.execute("UPDATE appts SET tg_id=? WHERE id=?", (m.from_user.id, a["id"]))
                c.commit()
                a = c.execute("SELECT * FROM appts WHERE id=?", (a["id"],)).fetchone()
            else:
                a = None
        if a:
            await state.clear()
            await m.answer("Нагадування підключено ✅\n\n" + text_confirm(a), reply_markup=kb_main())
            return
    await cmd_start(m, state)


@router.message(CommandStart())
@router.message(Command("menu"))
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(
        f"Вітаємо в «{SHOP_NAME}»! ✂️\n\nКнопки внизу відкривають усі розділи, команди завжди в меню ☰ біля поля вводу.",
        reply_markup=kb_panel(m.from_user.id),
    )
    await m.answer("Що робимо?", reply_markup=kb_main())


@router.message(Command("cancel"))
async def cmd_cancel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Скасовано. Щоб почати спочатку, натисніть /start", reply_markup=ReplyKeyboardRemove())


def my_view(tg_id: int):
    with closing(db()) as c:
        rows = c.execute(
            "SELECT * FROM appts WHERE tg_id=? AND status='booked' AND start>? ORDER BY start",
            (tg_id, now().isoformat(timespec="seconds")),
        ).fetchall()
    b = InlineKeyboardBuilder()
    if not rows:
        b.button(text="Записатися", callback_data="book")
        b.adjust(1)
        return "У вас немає майбутніх записів.", b.as_markup()
    lines = ["Ваші записи:\n"]
    for r in rows:
        lines.append(f"• {fmt(datetime.fromisoformat(r['start']))}, {SERVICES[r['service']][0]}, {master_name(r['master'])}")
        b.button(text=f"Скасувати {datetime.fromisoformat(r['start']):%d.%m %H:%M}", callback_data=f"x:{r['id']}")
    b.button(text="‹ Назад", callback_data="home")
    b.adjust(1)
    return "\n".join(lines), b.as_markup()


@router.message(Command("my"))
async def cmd_my(m: Message):
    text, kb = my_view(m.from_user.id)
    await m.answer(text, reply_markup=kb)


def day_view(day: date) -> str:
    with closing(db()) as c:
        rows = c.execute(
            "SELECT * FROM appts WHERE status='booked' AND substr(start,1,10)=? ORDER BY start",
            (day.isoformat(),),
        ).fetchall()
    if not rows:
        return f"{day:%d.%m.%Y}: записів немає."
    lines = [f"Записи на {day:%d.%m.%Y}:\n"]
    for r in rows:
        st = datetime.fromisoformat(r["start"])
        src = "сайт" if r["source"] == "web" else "бот"
        lines.append(
            f"{st:%H:%M} · {r['name']} · {r['phone']}\n   {SERVICES[r['service']][0]}, {master_name(r['master'])} ({src})"
        )
    return "\n".join(lines)


@router.message(Command("today"))
async def cmd_today(m: Message):
    if m.from_user.id in ADMIN_IDS:
        await m.answer(day_view(now().date()))


@router.message(Command("tomorrow"))
async def cmd_tomorrow(m: Message):
    if m.from_user.id in ADMIN_IDS:
        await m.answer(day_view(now().date() + timedelta(days=1)))


# ---------- Постійна панель знизу та команди ----------
PANEL = {
    "book": "📅 Записатися", "my": "📋 Мої записи", "info": "💈 Ціни", "bonus": "⭐ Бонуси",
    "contacts": "📍 Контакти", "site": "🌐 Сайт", "today": "📊 Сьогодні", "tomorrow": "📆 Завтра",
}


def kb_panel(user_id: int):
    rows = [
        [KeyboardButton(text=PANEL["book"]), KeyboardButton(text=PANEL["my"])],
        [KeyboardButton(text=PANEL["info"]), KeyboardButton(text=PANEL["bonus"])],
        [KeyboardButton(text=PANEL["contacts"])],
    ]
    if PUBLIC_URL.startswith("https://"):
        rows[2].append(KeyboardButton(text=PANEL["site"], web_app=WebAppInfo(url=PUBLIC_URL)))
    if user_id in ADMIN_IDS:
        rows.append([KeyboardButton(text=PANEL["today"]), KeyboardButton(text=PANEL["tomorrow"])])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True)


def bonus_text(tg_id: int) -> str:
    if LOYALTY_EVERY <= 0:
        return "Програма лояльності зараз не діє."
    with closing(db()) as c:
        done = c.execute("SELECT COUNT(*) FROM appts WHERE tg_id=? AND status='done'", (tg_id,)).fetchone()[0]
        cnt = c.execute("SELECT COUNT(*) FROM appts WHERE tg_id=? AND status IN ('done','booked')", (tg_id,)).fetchone()[0]
    left = (-(cnt + 1)) % LOYALTY_EVERY
    goal = "🎉 Ваш наступний запис буде зі знижкою!" if left == 0 else f"До знижки залишилось записів: {left}"
    return f"⭐ Програма лояльності\n\nКожен {LOYALTY_EVERY}-й запис зі знижкою {LOYALTY_PERCENT}%.\nЗавершених візитів: {done}\n{goal}"


@router.message(Command("book"))
@router.message(F.text == PANEL["book"])
async def pn_book(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Оберіть послугу:", reply_markup=kb_services())


@router.message(F.text == PANEL["my"])
async def pn_my(m: Message, state: FSMContext):
    await state.clear()
    await cmd_my(m)


@router.message(Command("info"))
@router.message(F.text == PANEL["info"])
async def pn_info(m: Message, state: FSMContext):
    await state.clear()
    text, kb = info_view()
    await m.answer(text, reply_markup=kb)


@router.message(Command("contacts"))
@router.message(F.text == PANEL["contacts"])
async def pn_contacts(m: Message, state: FSMContext):
    await state.clear()
    extra = f"\n🌐 {PUBLIC_URL}" if PUBLIC_URL else ""
    await m.answer(f"{SHOP_NAME}\n📍 {ADDRESS}\n🕒 Щодня {OPEN_HOUR}:00–{OPEN_HOUR + SLOTS // 2}:00{extra}")


@router.message(Command("bonus"))
@router.message(F.text == PANEL["bonus"])
async def pn_bonus(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(bonus_text(m.from_user.id))


@router.message(F.text == PANEL["today"])
async def pn_today(m: Message):
    await cmd_today(m)


@router.message(F.text == PANEL["tomorrow"])
async def pn_tomorrow(m: Message):
    await cmd_tomorrow(m)


@router.callback_query(F.data.startswith("ok:"))
async def cb_ok(cb: CallbackQuery, bot: Bot):
    appt_id = int(cb.data.split(":")[1])
    with closing(db()) as c:
        a = c.execute("SELECT * FROM appts WHERE id=? AND tg_id=? AND status='booked'", (appt_id, cb.from_user.id)).fetchone()
    if not a:
        await cb.answer("Запис не знайдено.", show_alert=True)
        return
    await show(cb, cb.message.text + "\n\n✅ Чекаємо на вас!")
    await notify_admins(bot, f"✅ Клієнт підтвердив візит\n{a['name']} · {fmt(datetime.fromisoformat(a['start']))}")


@router.callback_query(F.data.startswith("r:"))
async def cb_rate(cb: CallbackQuery, bot: Bot):
    _, aid, n = cb.data.split(":")
    aid, n = int(aid), int(n)
    if not 1 <= n <= 5:
        return await cb.answer()
    with closing(db()) as c:
        a = c.execute("SELECT * FROM appts WHERE id=? AND tg_id=?", (aid, cb.from_user.id)).fetchone()
        if not a:
            return await cb.answer()
        if c.execute("SELECT 1 FROM reviews WHERE appt_id=?", (aid,)).fetchone():
            return await cb.answer("Дякуємо, оцінку вже враховано.", show_alert=True)
        c.execute("INSERT INTO reviews(appt_id, tg_id, rating, created) VALUES(?,?,?,?)", (aid, cb.from_user.id, n, now().isoformat(timespec="seconds")))
        c.commit()
    await show(cb, f"Дякуємо за оцінку {'⭐' * n}! Чекаємо вас знову ✂️")
    if n <= 3:
        await notify_admins(bot, f"⚠️ Низька оцінка {n}/5\n{a['name']} · {a['phone']}\nМайстер: {master_name(a['master'])}")


# ---------- Меню та кроки запису ----------
@router.callback_query(F.data == "home")
async def cb_home(cb: CallbackQuery):
    await show(cb, f"«{SHOP_NAME}»\n\nОберіть дію:", kb_main())


def info_view():
    lines = ["Ціни:\n"]
    for name, mins, price in SERVICES.values():
        lines.append(f"• {name}, {mins} хв: {price} ₴")
    if LOYALTY_EVERY > 0:
        lines.append(f"\n⭐ Кожен {LOYALTY_EVERY}-й запис зі знижкою {LOYALTY_PERCENT}%")
    lines.append(f"\n📍 {ADDRESS}")
    lines.append(f"🕒 Щодня {OPEN_HOUR}:00–{OPEN_HOUR + SLOTS // 2}:00")
    b = InlineKeyboardBuilder()
    b.button(text="Записатися", callback_data="book")
    b.button(text="‹ Назад", callback_data="home")
    b.adjust(1)
    return "\n".join(lines), b.as_markup()


@router.callback_query(F.data == "info")
async def cb_info(cb: CallbackQuery):
    text, kb = info_view()
    await show(cb, text, kb)


@router.callback_query(F.data == "book")
async def cb_book(cb: CallbackQuery):
    await show(cb, "Оберіть послугу:", kb_services())


@router.callback_query(F.data.startswith("s:"))
async def cb_service(cb: CallbackQuery):
    sid = cb.data.split(":")[1]
    if sid not in SERVICES:
        return await cb.answer()
    await show(cb, "Оберіть майстра:", kb_masters(sid))


@router.callback_query(F.data.startswith("m:"))
async def cb_master(cb: CallbackQuery):
    _, sid, mid = cb.data.split(":")
    if sid not in SERVICES or mid not in VALID_MASTERS:
        return await cb.answer()
    b = InlineKeyboardBuilder()
    today = now().date()
    any_days = False
    for k in range(BOOK_DAYS):
        day = today + timedelta(days=k)
        if free_slots(day, mid, sid):
            any_days = True
            b.button(text=f"{WEEKDAYS[day.weekday()]} {day:%d.%m}", callback_data=f"d:{sid}:{mid}:{day.isoformat()}")
    b.adjust(3)
    b.row(InlineKeyboardButton(text="‹ Назад", callback_data=f"s:{sid}"))
    text = "Оберіть дату:" if any_days else "На найближчий тиждень вільних вікон немає. Спробуйте іншого майстра."
    await show(cb, text, b.as_markup())


@router.callback_query(F.data.startswith("d:"))
async def cb_date(cb: CallbackQuery):
    _, sid, mid, d = cb.data.split(":")
    if sid not in SERVICES or mid not in VALID_MASTERS:
        return await cb.answer()
    day = date.fromisoformat(d)
    slots = free_slots(day, mid, sid)
    b = InlineKeyboardBuilder()
    for i in slots:
        b.button(text=slot_label(i), callback_data=f"t:{sid}:{mid}:{d}:{i}")
    b.adjust(4)
    b.row(InlineKeyboardButton(text="‹ Назад", callback_data=f"m:{sid}:{mid}"))
    text = f"{day:%d.%m.%Y}. Вільний час:" if slots else "На цей день вільних вікон немає."
    await show(cb, text, b.as_markup())


@router.callback_query(F.data.startswith("t:"))
async def cb_time(cb: CallbackQuery, state: FSMContext):
    _, sid, mid, d, i = cb.data.split(":")
    if sid not in SERVICES or mid not in VALID_MASTERS:
        return await cb.answer()
    day, i = date.fromisoformat(d), int(i)
    if i not in free_slots(day, mid, sid):
        await cb.answer("Цей час уже зайнятий. Оберіть інший.", show_alert=True)
        return
    await state.set_state(Booking.phone)
    await state.update_data(sid=sid, mid=mid, day=d, slot=i)
    name, mins, price = SERVICES[sid]
    kb = ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📱 Поділитися номером", request_contact=True)]],
        resize_keyboard=True,
        one_time_keyboard=True,
    )
    await cb.message.answer(
        f"{name}, {master_name(mid)}\n📅 {fmt(slot_dt(day, i))}\n💰 {price} ₴\n\n"
        "Залишилось вказати номер телефону. Натисніть кнопку нижче "
        "або напишіть номер у форматі 0501234567.\n\nСкасувати: /cancel",
        reply_markup=kb,
    )
    await cb.answer()


@router.message(Booking.phone, F.contact)
@router.message(Booking.phone, F.text)
async def got_phone(m: Message, state: FSMContext, bot: Bot):
    raw = m.contact.phone_number if m.contact else m.text
    phone = normalize_phone(raw)
    if not phone:
        await m.answer("Не схоже на український номер. Напишіть у форматі 0501234567.")
        return
    data = await state.get_data()
    try:
        appt = await create_appointment(
            name=m.from_user.full_name,
            phone=phone,
            sid=data["sid"],
            mid=data["mid"],
            day=date.fromisoformat(data["day"]),
            slot=data["slot"],
            tg_id=m.from_user.id,
            source="bot",
        )
    except BookingError as e:
        await state.clear()
        await m.answer(f"{e}\n\nПочати спочатку: /start", reply_markup=ReplyKeyboardRemove())
        return
    await state.clear()
    await m.answer("Готово!", reply_markup=ReplyKeyboardRemove())
    await after_booking(bot, appt)


# ---------- Мої записи ----------
@router.callback_query(F.data == "my")
async def cb_my(cb: CallbackQuery):
    text, kb = my_view(cb.from_user.id)
    await show(cb, text, kb)


@router.callback_query(F.data.startswith("x:"))
async def cb_cancel(cb: CallbackQuery, bot: Bot):
    appt_id = int(cb.data.split(":")[1])
    with closing(db()) as c:
        a = c.execute(
            "SELECT * FROM appts WHERE id=? AND tg_id=? AND status='booked'", (appt_id, cb.from_user.id)
        ).fetchone()
        if a:
            c.execute("UPDATE appts SET status='cancelled' WHERE id=?", (appt_id,))
            c.commit()
    if not a:
        await cb.answer("Запис не знайдено.", show_alert=True)
        return
    await notify_admins(
        bot, f"❌ Запис скасовано\n{a['name']} · {a['phone']}\n{fmt(datetime.fromisoformat(a['start']))}"
    )
    text, kb = my_view(cb.from_user.id)
    await show(cb, "Запис скасовано.\n\n" + text, kb)


# ---------- Фонова перевірка нагадувань ----------
async def reminder_loop(bot) -> None:
    while True:
        try:
            current = now().isoformat(timespec="seconds")
            with closing(db()) as c:
                rows = c.execute(
                    """
                    SELECT r.id AS rid, r.appt_id AS aid, r.kind, a.tg_id, a.phone, a.service, a.master, a.start
                    FROM reminders r JOIN appts a ON a.id = r.appt_id
                    WHERE r.sent = 0 AND r.send_at <= ? AND a.status = 'booked'
                    """,
                    (current,),
                ).fetchall()
            for r in rows:
                if datetime.fromisoformat(r["start"]) > now():
                    await notify_client(bot, r, text_reminder(r["kind"], r), sms_reminder(r), kb_remind(r["aid"]))
                with closing(db()) as c:
                    c.execute("UPDATE reminders SET sent=1 WHERE id=?", (r["rid"],))
                    c.commit()
        except Exception:
            logging.exception("Помилка в циклі нагадувань")
        await asyncio.sleep(30)


# ---------- Сайт і API ----------
RATE: dict = {}


def client_ip(request) -> str:
    """За проксі (Railway, Render, Heroku) справжній IP лежить у X-Forwarded-For."""
    fwd = request.headers.get("X-Forwarded-For", "")
    return fwd.split(",")[0].strip() if fwd else (request.remote or "?")


def rate_limited(ip: str, limit: int = 8, window: int = 3600) -> bool:
    t = _time.time()
    hits = [x for x in RATE.get(ip, []) if t - x < window]
    if len(hits) >= limit:
        RATE[ip] = hits
        return True
    hits.append(t)
    RATE[ip] = hits
    return False


def parse_day(s: str):
    try:
        d = date.fromisoformat(s)
    except (ValueError, TypeError):
        return None
    today = now().date()
    return d if today <= d <= today + timedelta(days=BOOK_DAYS - 1) else None


def jerr(text: str, status: int = 400):
    return web.json_response({"ok": False, "error": text}, status=status)


@web.middleware
async def cors(request, handler):
    resp = web.Response() if request.method == "OPTIONS" else await handler(request)
    if ALLOWED_ORIGIN:
        resp.headers["Access-Control-Allow-Origin"] = ALLOWED_ORIGIN
        resp.headers["Access-Control-Allow-Headers"] = "Content-Type, X-Session"
        resp.headers["Access-Control-Allow-Methods"] = "GET,POST,OPTIONS"
    return resp


async def healthz(request):
    return web.Response(text="ok")


async def options(request):
    return web.Response()


async def api_config(request):
    return web.json_response(
        {
            "ok": True,
            "shop": SHOP_NAME,
            "address": ADDRESS,
            "hours": f"{OPEN_HOUR}:00–{OPEN_HOUR + SLOTS // 2}:00",
            "bot": BOT_USERNAME,
            "services": [{"id": k, "name": v[0], "min": v[1], "price": v[2]} for k, v in SERVICES.items()],
            "masters": [{"id": k, "name": v} for k, v in MASTERS.items()],
        }
    )


async def api_days(request):
    sid, mid = request.query.get("service"), request.query.get("master")
    if sid not in SERVICES or mid not in VALID_MASTERS:
        return jerr("Невірні параметри.")
    today = now().date()
    days = []
    for k in range(BOOK_DAYS):
        d = today + timedelta(days=k)
        if free_slots(d, mid, sid):
            days.append({"date": d.isoformat(), "label": f"{WEEKDAYS[d.weekday()]} {d:%d.%m}"})
    return web.json_response({"ok": True, "days": days})


async def api_slots(request):
    sid, mid = request.query.get("service"), request.query.get("master")
    day = parse_day(request.query.get("date", ""))
    if sid not in SERVICES or mid not in VALID_MASTERS or not day:
        return jerr("Невірні параметри.")
    return web.json_response(
        {"ok": True, "slots": [{"i": i, "label": slot_label(i)} for i in free_slots(day, mid, sid)]}
    )


async def api_book(request):
    if rate_limited(client_ip(request)):
        return jerr("Забагато спроб. Спробуйте пізніше.", 429)
    try:
        data = await request.json()
    except Exception:
        return jerr("Невірний запит.")
    if not isinstance(data, dict):
        return jerr("Невірний запит.")
    if data.get("website"):  # приманка для ботів: людина це поле не бачить
        return web.json_response({"ok": True})
    sid, mid = data.get("service"), data.get("master")
    day = parse_day(str(data.get("date", "")))
    slot = data.get("slot")
    name = str(data.get("name", "")).strip()[:60]
    phone = normalize_phone(str(data.get("phone", "")))
    if sid not in SERVICES or mid not in VALID_MASTERS or not day or not isinstance(slot, int) or isinstance(slot, bool):
        return jerr("Невірні параметри запису.")
    if len(name) < 2:
        return jerr("Вкажіть ім'я.")
    if not phone:
        return jerr("Вкажіть український номер у форматі 0501234567.")
    sess = get_session(request)
    try:
        appt = await create_appointment(
            name=name, phone=phone, sid=sid, mid=mid, day=day, slot=slot, tg_id=sess["tg_id"] if sess else None, source="web"
        )
    except BookingError as e:
        return jerr(str(e), 409)
    await after_booking(request.app["bot"], appt)
    s = SERVICES[sid]
    return web.json_response(
        {
            "ok": True,
            "when": fmt(datetime.fromisoformat(appt["start"])),
            "service": s[0],
            "master": master_name(appt["master"]),
            "price": appt["price"] if appt["price"] is not None else s[2],
            "logged": bool(sess),
            "tg_link": f"https://t.me/{BOT_USERNAME}?start=link_{appt['token']}" if BOT_USERNAME else None,
        }
    )


async def index(request):
    f = WEB_DIR / "index.html"
    if not f.exists():
        return web.Response(text="Сайт не знайдено (папка web/index.html).", status=404)
    return web.FileResponse(f)


# ---------- Адмін-панель ----------
ADMIN_TOKEN = os.getenv("ADMIN_PANEL_TOKEN", "")
ADMIN_STATUS = {"booked": "Очікується", "done": "Завершено", "cancelled": "Скасовано"}


def admin_ok(request) -> bool:
    """Токен приймається лише із заголовка, щоб він не потрапляв у URL і логи."""
    if not ADMIN_TOKEN:
        return False
    return secrets.compare_digest(request.headers.get("X-Admin-Token", ""), ADMIN_TOKEN)


def no_access():
    return web.json_response({"ok": False, "error": "Немає доступу"}, status=403)


SRC = {"web": "сайт", "admin": "CRM"}


def parse_any_day(s):
    try:
        return date.fromisoformat(s)
    except (ValueError, TypeError):
        return None


async def admin_day(request):
    if not admin_ok(request):
        return no_access()
    today = now().date()
    d1 = parse_any_day(request.query.get("start", "")) or today
    d2 = parse_any_day(request.query.get("end", "")) or d1
    if d1 > d2:
        d1, d2 = d2, d1
    q = request.query.get("q", "").strip().lower()
    mf, sf = request.query.get("master", ""), request.query.get("status", "")
    with closing(db()) as c:
        rows = c.execute(
            "SELECT * FROM appts WHERE substr(start,1,10) BETWEEN ? AND ? ORDER BY start", (d1.isoformat(), d2.isoformat())
        ).fetchall()
    items, by_master, by_service = [], {}, {}
    for r in rows:
        st = datetime.fromisoformat(r["start"])
        svc = SERVICES.get(r["service"], ("?", 0, 0))
        price = r["price"] if r["price"] is not None else svc[2]
        mname = MASTERS.get(r["master"], r["master"])
        if (mf and r["master"] != mf) or (sf and r["status"] != sf) or (q and q not in f"{r['name']} {r['phone']}".lower()):
            continue
        items.append(
            {
                "id": r["id"], "date": f"{st:%d.%m}", "time": f"{st:%H:%M}", "name": r["name"], "phone": r["phone"],
                "service": svc[0], "master": mname, "price": price, "status": r["status"],
                "source": SRC.get(r["source"], "бот"), "tg": bool(r["tg_id"]), "note": r["note"] or "",
            }
        )
        if r["status"] != "cancelled":
            m = by_master.setdefault(mname, {"n": 0, "revenue": 0})
            m["n"] += 1
            m["revenue"] += price if r["status"] == "done" else 0
            by_service[svc[0]] = by_service.get(svc[0], 0) + 1
    done = [i for i in items if i["status"] == "done"]
    revenue = sum(i["price"] for i in done)
    return web.json_response(
        {
            "ok": True,
            "items": items,
            "stats": {
                "count": len([i for i in items if i["status"] != "cancelled"]),
                "done_count": len(done),
                "revenue": revenue,
                "avg_check": revenue // len(done) if done else 0,
                "expected": sum(i["price"] for i in items if i["status"] == "booked"),
                "lost_revenue": sum(i["price"] for i in items if i["status"] == "cancelled"),
                "by_master": by_master,
                "by_service": dict(sorted(by_service.items(), key=lambda x: -x[1])),
            },
        }
    )


async def admin_status(request):
    if not admin_ok(request):
        return no_access()
    try:
        data = await request.json()
        appt_id = int(data.get("id", 0))
        status = str(data.get("status", ""))
    except Exception:
        return jerr("Невірний запит.")
    if status not in ADMIN_STATUS:
        return jerr("Невірний статус.")
    with closing(db()) as c:
        a = c.execute("SELECT * FROM appts WHERE id=?", (appt_id,)).fetchone()
        if not a:
            return jerr("Запис не знайдено.", 404)
        if status == "booked" and a["status"] == "cancelled" and a["service"] in SERVICES:
            # повернути скасований запис можна лише якщо час досі вільний
            st = datetime.fromisoformat(a["start"])
            i = ((st.hour * 60 + st.minute) - OPEN_HOUR * 60) // 30
            need = {i + k for k in range(units(a["service"]))}
            if need & busy_slots(st.date(), a["master"], skip_id=appt_id):
                return jerr("Цей час уже зайнятий іншим записом.", 409)
        c.execute("UPDATE appts SET status=? WHERE id=?", (status, appt_id))
        c.commit()
    if a["status"] != status:
        label = ADMIN_STATUS[status]
        try:
            if status == "done":
                await send_review_request(request.app["bot"], a)
            elif status == "cancelled" and a["tg_id"]:
                await request.app["bot"].send_message(
                    a["tg_id"], f"❌ Ваш запис на {fmt(datetime.fromisoformat(a['start']))} скасовано адміністратором. Обрати інший час: /book"
                )
        except Exception:
            logging.exception("Не вдалося сповістити клієнта про зміну статусу")
        try:
            await notify_admins(
                request.app["bot"],
                f"📝 Статус запису: {label}\n{a['name']} · {a['phone']}\n{fmt(datetime.fromisoformat(a['start']))}",
            )
        except Exception:
            logging.exception("Не вдалося сповістити адмінів про зміну статусу")
    return web.json_response({"ok": True})


async def admin_clients(request):
    if not admin_ok(request):
        return no_access()
    with closing(db()) as c:
        rows = c.execute("SELECT name, phone, service, start, status, tg_id, price FROM appts").fetchall()
    today = now().date()
    clients: dict = {}
    for r in rows:
        p = r["phone"] or "?"
        cinfo = clients.setdefault(
            p, {"name": r["name"], "phone": p, "visits": 0, "spent": 0, "last": None, "upcoming": False, "tg": False}
        )
        if r["name"]:
            cinfo["name"] = r["name"]
        if r["tg_id"]:
            cinfo["tg"] = True
        if r["status"] == "done":
            cinfo["visits"] += 1
            cinfo["spent"] += r["price"] if r["price"] is not None else SERVICES.get(r["service"], ("", 0, 0))[2]
            d = r["start"][:10]
            if not cinfo["last"] or d > cinfo["last"]:
                cinfo["last"] = d
        if r["status"] == "booked" and r["start"][:10] >= today.isoformat():
            cinfo["upcoming"] = True
    return web.json_response({"ok": True, "clients": sorted(clients.values(), key=lambda x: -x["spent"])})


async def admin_page(request):
    f = WEB_DIR / "admin.html"
    if not ADMIN_TOKEN or not f.exists():
        return web.Response(text="Адмін-панель не налаштована (ADMIN_PANEL_TOKEN).", status=404)
    return web.FileResponse(f)


# ---------- Вхід через Telegram і особистий кабінет ----------
def get_session(request):
    tok = request.headers.get("X-Session", "")
    if not tok:
        return None
    cutoff = (now() - timedelta(days=30)).isoformat(timespec="seconds")
    with closing(db()) as c:
        return c.execute("SELECT * FROM sessions WHERE token=? AND created>?", (tok, cutoff)).fetchone()


async def api_auth_start(request):
    if not BOT_USERNAME:
        return jerr("Бот не налаштований.", 503)
    if rate_limited("auth:" + client_ip(request), limit=20):
        return jerr("Забагато спроб. Спробуйте пізніше.", 429)
    tok = secrets.token_urlsafe(12)
    with closing(db()) as c:
        c.execute("INSERT INTO auth_tokens(token, created) VALUES(?,?)", (tok, now().isoformat(timespec="seconds")))
        c.commit()
    return web.json_response({"ok": True, "token": tok, "link": f"https://t.me/{BOT_USERNAME}?start=login_{tok}"})


async def api_auth_check(request):
    tok = request.query.get("token", "")
    cutoff = (now() - timedelta(minutes=10)).isoformat(timespec="seconds")
    with closing(db()) as c:
        row = c.execute("SELECT * FROM auth_tokens WHERE token=? AND created>?", (tok, cutoff)).fetchone()
        if not row:
            return jerr("Час входу минув. Спробуйте ще раз.", 410)
        if not row["tg_id"]:
            return web.json_response({"ok": True, "status": "wait"})
        sess = secrets.token_urlsafe(24)
        c.execute("INSERT INTO sessions(token, tg_id, name, created) VALUES(?,?,?,?)", (sess, row["tg_id"], row["name"], now().isoformat(timespec="seconds")))
        c.execute("DELETE FROM auth_tokens WHERE token=?", (tok,))
        c.commit()
    return web.json_response({"ok": True, "status": "ok", "session": sess, "name": row["name"]})


async def api_logout(request):
    s = get_session(request)
    if s:
        with closing(db()) as c:
            c.execute("DELETE FROM sessions WHERE token=?", (s["token"],))
            c.commit()
    return web.json_response({"ok": True})


async def api_me(request):
    s = get_session(request)
    if not s:
        return jerr("Потрібен вхід.", 401)
    with closing(db()) as c:
        rows = c.execute("SELECT * FROM appts WHERE tg_id=? ORDER BY start DESC LIMIT 30", (s["tg_id"],)).fetchall()
    cur = now().isoformat(timespec="seconds")
    cnt = len([r for r in rows if r["status"] in ("done", "booked")])
    items = [
        {
            "id": r["id"], "when": fmt(datetime.fromisoformat(r["start"])), "status": r["status"],
            "service": SERVICES.get(r["service"], ("?",))[0], "master": master_name(r["master"]),
            "price": r["price"] if r["price"] is not None else SERVICES.get(r["service"], (0, 0, 0))[2],
            "upcoming": r["status"] == "booked" and r["start"] > cur,
        }
        for r in rows
    ]
    return web.json_response(
        {
            "ok": True, "name": s["name"], "phone": rows[0]["phone"] if rows else "", "items": items,
            "bonus": ((-(cnt + 1)) % LOYALTY_EVERY) if LOYALTY_EVERY > 0 else None,
            "bonus_every": LOYALTY_EVERY, "bonus_percent": LOYALTY_PERCENT,
        }
    )


async def api_me_cancel(request):
    s = get_session(request)
    if not s:
        return jerr("Потрібен вхід.", 401)
    try:
        appt_id = int((await request.json()).get("id", 0))
    except Exception:
        return jerr("Невірний запит.")
    with closing(db()) as c:
        a = c.execute("SELECT * FROM appts WHERE id=? AND tg_id=? AND status='booked'", (appt_id, s["tg_id"])).fetchone()
        if not a:
            return jerr("Запис не знайдено.", 404)
        c.execute("UPDATE appts SET status='cancelled' WHERE id=?", (appt_id,))
        c.commit()
    await notify_admins(request.app["bot"], f"❌ Запис скасовано (сайт)\n{a['name']} · {a['phone']}\n{fmt(datetime.fromisoformat(a['start']))}")
    return web.json_response({"ok": True})


# ---------- CRM: розклад, ручний запис, нотатки, повідомлення, розсилка, відгуки, експорт ----------
async def admin_schedule(request):
    if not admin_ok(request):
        return no_access()
    day = parse_any_day(request.query.get("date", "")) or now().date()
    with closing(db()) as c:
        rows = c.execute("SELECT * FROM appts WHERE status!='cancelled' AND substr(start,1,10)=?", (day.isoformat(),)).fetchall()
    cells = {m: [None] * SLOTS for m in MASTERS}
    for r in rows:
        if r["master"] not in cells or r["service"] not in SERVICES:
            continue
        st = datetime.fromisoformat(r["start"])
        i = ((st.hour * 60 + st.minute) - OPEN_HOUR * 60) // 30
        if not 0 <= i < SLOTS:
            continue
        span = min(units(r["service"]), SLOTS - i)
        cells[r["master"]][i] = {"id": r["id"], "name": r["name"], "service": SERVICES[r["service"]][0], "status": r["status"], "span": span}
        for k in range(1, span):
            cells[r["master"]][i + k] = "skip"
    return web.json_response(
        {"ok": True, "masters": [{"id": k, "name": v} for k, v in MASTERS.items()], "slots": [slot_label(i) for i in range(SLOTS)], "cells": cells}
    )


async def admin_free(request):
    if not admin_ok(request):
        return no_access()
    sid, mid = request.query.get("service"), request.query.get("master")
    day = parse_any_day(request.query.get("date", ""))
    if sid not in SERVICES or mid not in VALID_MASTERS or not day:
        return jerr("Невірні параметри.")
    return web.json_response({"ok": True, "slots": [{"i": i, "label": slot_label(i)} for i in free_slots(day, mid, sid, 0)]})


async def admin_create(request):
    if not admin_ok(request):
        return no_access()
    try:
        d = await request.json()
    except Exception:
        return jerr("Невірний запит.")
    sid, mid, slot = d.get("service"), d.get("master"), d.get("slot")
    day = parse_any_day(str(d.get("date", "")))
    name = str(d.get("name", "")).strip()[:60]
    phone = normalize_phone(str(d.get("phone", "")))
    if sid not in SERVICES or mid not in VALID_MASTERS or not day or not isinstance(slot, int) or isinstance(slot, bool):
        return jerr("Невірні параметри запису.")
    if len(name) < 2 or not phone:
        return jerr("Вкажіть ім'я та український номер.")
    with closing(db()) as c:
        row = c.execute("SELECT tg_id FROM appts WHERE phone=? AND tg_id IS NOT NULL ORDER BY id DESC LIMIT 1", (phone,)).fetchone()
    try:
        appt = await create_appointment(
            name=name, phone=phone, sid=sid, mid=mid, day=day, slot=slot,
            tg_id=row["tg_id"] if row else None, source="admin", admin=True, note=str(d.get("note", ""))[:200],
        )
    except BookingError as e:
        return jerr(str(e), 409)
    await after_booking(request.app["bot"], appt)
    return web.json_response({"ok": True})


async def admin_note(request):
    if not admin_ok(request):
        return no_access()
    try:
        d = await request.json()
        appt_id, note = int(d.get("id", 0)), str(d.get("note", ""))[:200]
    except Exception:
        return jerr("Невірний запит.")
    with closing(db()) as c:
        c.execute("UPDATE appts SET note=? WHERE id=?", (note, appt_id))
        c.commit()
    return web.json_response({"ok": True})


async def admin_message(request):
    if not admin_ok(request):
        return no_access()
    try:
        d = await request.json()
        phone, text = str(d.get("phone", "")), str(d.get("text", "")).strip()[:1000]
    except Exception:
        return jerr("Невірний запит.")
    with closing(db()) as c:
        row = c.execute("SELECT tg_id FROM appts WHERE phone=? AND tg_id IS NOT NULL ORDER BY id DESC LIMIT 1", (phone,)).fetchone()
    if not row or not text:
        return jerr("Клієнт не підключив Telegram, або текст порожній.")
    try:
        await request.app["bot"].send_message(row["tg_id"], text)
    except Exception:
        return jerr("Telegram не прийняв повідомлення (клієнт міг заблокувати бота).")
    return web.json_response({"ok": True})


async def admin_broadcast(request):
    if not admin_ok(request):
        return no_access()
    try:
        text = str((await request.json()).get("text", "")).strip()[:3000]
    except Exception:
        return jerr("Невірний запит.")
    if not text:
        return jerr("Введіть текст розсилки.")
    with closing(db()) as c:
        ids = [r[0] for r in c.execute("SELECT DISTINCT tg_id FROM appts WHERE tg_id IS NOT NULL")]
    sent = 0
    for tg in ids:
        try:
            await request.app["bot"].send_message(tg, text)
            sent += 1
        except Exception:
            pass
        await asyncio.sleep(0.05)
    return web.json_response({"ok": True, "sent": sent, "total": len(ids)})


async def admin_reviews(request):
    if not admin_ok(request):
        return no_access()
    with closing(db()) as c:
        rows = c.execute(
            "SELECT r.rating, r.created, a.name, a.master, a.service FROM reviews r JOIN appts a ON a.id=r.appt_id ORDER BY r.id DESC LIMIT 100"
        ).fetchall()
    items = [{"rating": r["rating"], "date": r["created"][:10], "name": r["name"], "master": master_name(r["master"]), "service": SERVICES.get(r["service"], ("?",))[0]} for r in rows]
    avg = round(sum(i["rating"] for i in items) / len(items), 2) if items else 0
    return web.json_response({"ok": True, "items": items, "avg": avg})


async def admin_export(request):
    if not admin_ok(request):
        return no_access()
    d1 = parse_any_day(request.query.get("start", "")) or now().date()
    d2 = parse_any_day(request.query.get("end", "")) or d1
    with closing(db()) as c:
        rows = c.execute("SELECT * FROM appts WHERE substr(start,1,10) BETWEEN ? AND ? ORDER BY start", (d1.isoformat(), d2.isoformat())).fetchall()
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(["Дата", "Час", "Клієнт", "Телефон", "Послуга", "Майстер", "Ціна", "Статус", "Джерело", "Нотатка"])
    for r in rows:
        st = datetime.fromisoformat(r["start"])
        svc = SERVICES.get(r["service"], ("?", 0, 0))
        w.writerow([f"{st:%d.%m.%Y}", f"{st:%H:%M}", r["name"], r["phone"], svc[0], master_name(r["master"]),
                    r["price"] if r["price"] is not None else svc[2], ADMIN_STATUS.get(r["status"], r["status"]), SRC.get(r["source"], "бот"), r["note"] or ""])
    return web.Response(text="\ufeff" + buf.getvalue(), content_type="text/csv", charset="utf-8")


async def setup_bot_ui(bot) -> None:
    """Меню команд (☰ біля поля вводу) і кнопка «Сайт»."""
    base = [
        BotCommand(command="start", description="Головне меню"),
        BotCommand(command="book", description="Записатися"),
        BotCommand(command="my", description="Мої записи"),
        BotCommand(command="info", description="Ціни"),
        BotCommand(command="contacts", description="Адреса та години"),
        BotCommand(command="bonus", description="Бонуси і знижки"),
        BotCommand(command="cancel", description="Скасувати поточну дію"),
    ]
    admin_extra = [BotCommand(command="today", description="Записи на сьогодні"), BotCommand(command="tomorrow", description="Записи на завтра")]
    try:
        await bot.set_my_commands(base)
        if PUBLIC_URL.startswith("https://"):
            await bot.set_chat_menu_button(menu_button=MenuButtonWebApp(text="Сайт", web_app=WebAppInfo(url=PUBLIC_URL)))
    except Exception:
        logging.exception("Не вдалося налаштувати меню бота")
    for aid in ADMIN_IDS:
        try:
            await bot.set_my_commands(base + admin_extra, scope=BotCommandScopeChat(chat_id=aid))
        except Exception:
            logging.warning("Команди адміна не встановлено для %s (адмін ще не запускав бота)", aid)


def build_app(bot) -> web.Application:
    app = web.Application(middlewares=[cors])
    app["bot"] = bot
    app.router.add_get("/", index)
    app.router.add_get("/healthz", healthz)
    app.router.add_get("/admin", admin_page)
    app.router.add_get("/admin/api/day", admin_day)
    app.router.add_get("/admin/api/clients", admin_clients)
    app.router.add_post("/admin/api/status", admin_status)
    app.router.add_get("/api/config", api_config)
    app.router.add_get("/api/days", api_days)
    app.router.add_get("/api/slots", api_slots)
    app.router.add_post("/api/book", api_book)
    app.router.add_post("/api/auth/start", api_auth_start)
    app.router.add_get("/api/auth/check", api_auth_check)
    app.router.add_post("/api/auth/logout", api_logout)
    app.router.add_get("/api/me", api_me)
    app.router.add_post("/api/me/cancel", api_me_cancel)
    app.router.add_get("/admin/api/schedule", admin_schedule)
    app.router.add_get("/admin/api/free", admin_free)
    app.router.add_post("/admin/api/create", admin_create)
    app.router.add_post("/admin/api/note", admin_note)
    app.router.add_post("/admin/api/message", admin_message)
    app.router.add_post("/admin/api/broadcast", admin_broadcast)
    app.router.add_get("/admin/api/reviews", admin_reviews)
    app.router.add_get("/admin/api/export", admin_export)
    app.router.add_route("OPTIONS", "/api/{tail:.*}", options)
    return app


async def main() -> None:
    global BOT_USERNAME
    if not BOT_TOKEN:
        raise SystemExit("Не вказано BOT_TOKEN у файлі .env")
    logging.basicConfig(level=logging.INFO)
    init_db()
    bot = Bot(BOT_TOKEN)
    if not BOT_USERNAME:
        BOT_USERNAME = (await bot.get_me()).username or ""
    await setup_bot_ui(bot)
    runner = web.AppRunner(build_app(bot))
    await runner.setup()
    await web.TCPSite(runner, WEB_HOST, WEB_PORT).start()
    logging.info("Сайт працює на порту %s, бот @%s", WEB_PORT, BOT_USERNAME)
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    task = asyncio.create_task(reminder_loop(bot))
    try:
        await dp.start_polling(bot)
    finally:
        task.cancel()
        await runner.cleanup()


if __name__ == "__main__":
    asyncio.run(main())
