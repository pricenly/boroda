"""Барбершоп: Telegram-бот + сайт із записом + нагадування. Одна програма, одна база.

- Запис у боті й на сайті потрапляє в одну базу (SQLite), тому зайнятий час зникає в обох місцях.
- Нагадування: у день візиту (09:00) і приблизно за 4 години до запису (Telegram + SMS, якщо увімкнено).
- Клієнт із сайту може натиснути «Підключити нагадування в Telegram», і нагадування прийдуть у чат.
- Сайт (папка web/) віддається цією ж програмою, API: /api/config, /api/days, /api/slots, /api/book.
"""
import asyncio
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
    CallbackQuery,
    InlineKeyboardButton,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
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
DB_PATH = os.getenv("DB_PATH", "barber.db")

WEB_HOST = os.getenv("WEB_HOST", "0.0.0.0")
WEB_PORT = int(os.getenv("PORT", "8080"))
ALLOWED_ORIGIN = os.getenv("ALLOWED_ORIGIN", "")  # потрібно лише якщо сайт лежить на іншому домені
BOT_USERNAME = os.getenv("BOT_USERNAME", "")  # якщо порожньо, візьметься автоматично
WEB_DIR = Path(__file__).parent / "web"

SMS_ENABLED = os.getenv("SMS_ENABLED", "0") == "1"
TURBOSMS_TOKEN = os.getenv("TURBOSMS_TOKEN", "")
TURBOSMS_SENDER = os.getenv("TURBOSMS_SENDER", "")

# ---------- Послуги, майстри, графік ----------
SERVICES = {  # id: (назва, хвилин, ціна грн)
    "cut": ("Стрижка", 45, 400),
    "beard": ("Борода", 30, 250),
    "combo": ("Стрижка + борода", 75, 600),
    "kid": ("Дитяча стрижка", 30, 300),
}
MASTERS = {"a": "Андрій", "m": "Максим", "o": "Олег"}
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
    token TEXT
);
CREATE TABLE IF NOT EXISTS reminders(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    appt_id INTEGER,
    kind TEXT,
    send_at TEXT,
    sent INTEGER DEFAULT 0
);
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


def normalize_phone(raw: str):
    digits = re.sub(r"\D", "", raw or "")
    if len(digits) == 10 and digits.startswith("0"):
        digits = "38" + digits
    if len(digits) == 12 and digits.startswith("380"):
        return "+" + digits
    return None


def busy_slots(day: date, master: str) -> set:
    busy = set()
    with closing(db()) as c:
        rows = c.execute(
            "SELECT service, start FROM appts WHERE master=? AND status='booked' AND substr(start,1,10)=?",
            (master, day.isoformat()),
        ).fetchall()
    for r in rows:
        st = datetime.fromisoformat(r["start"])
        i = ((st.hour * 60 + st.minute) - OPEN_HOUR * 60) // 30
        for k in range(units(r["service"])):
            busy.add(i + k)
    return busy


def free_slots(day: date, master: str, service: str) -> list:
    busy = busy_slots(day, master)
    u = units(service)
    limit = now() + timedelta(minutes=30)  # записатися можна не пізніше ніж за 30 хв
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
    """Повертає [(тип, коли надіслати)].

    4h: за 4 години до запису, але не раніше 08:00 того ж дня.
    morning: о MORNING_HOUR в день візиту, якщо не збігається з 4h (різниця від 2 годин).
    Нагадування, час яких уже минув на момент запису, не створюються.
    """
    four = max(start - timedelta(hours=4), datetime.combine(start.date(), time(8)))
    morning = datetime.combine(start.date(), time(MORNING_HOUR))
    plan = [("4h", four)]
    if abs(four - morning) >= timedelta(hours=2) and morning <= start - timedelta(hours=2):
        plan.append(("morning", morning))
    return [(k, t) for k, t in plan if t > created]


# ---------- Єдина функція створення запису (бот і сайт) ----------
async def create_appointment(*, name, phone, sid, mid, day, slot, tg_id, source):
    async with LOCK:  # захист від двох записів на один час
        if slot not in free_slots(day, mid, sid):
            raise BookingError("На жаль, цей час щойно зайняли. Оберіть інший.")
        start = slot_dt(day, slot)
        with closing(db()) as c:
            active = c.execute(
                "SELECT COUNT(*) FROM appts WHERE phone=? AND status='booked' AND start>?",
                (phone, now().isoformat(timespec="seconds")),
            ).fetchone()[0]
            if active >= MAX_ACTIVE_PER_PHONE:
                raise BookingError("На цей номер уже оформлено кілька записів. Скасуйте зайвий або зателефонуйте нам.")
            cur = c.execute(
                "INSERT INTO appts(tg_id, name, phone, service, master, start, source, token) VALUES(?,?,?,?,?,?,?,?)",
                (tg_id, name, phone, sid, mid, start.isoformat(timespec="seconds"), source, secrets.token_urlsafe(8)),
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
    name, mins, price = SERVICES[a["service"]]
    return (
        "✅ Запис підтверджено\n\n"
        f"{SHOP_NAME}\n"
        f"📅 {fmt(datetime.fromisoformat(a['start']))}\n"
        f"✂️ {name}, {mins} хв\n"
        f"👤 Майстер: {MASTERS[a['master']]}\n"
        f"💰 {price} ₴\n"
        f"📍 {ADDRESS}\n\n"
        "Ми нагадаємо про візит. Якщо плани змінилися, скасуйте запис: /my"
    )


def text_reminder(kind: str, a) -> str:
    st = datetime.fromisoformat(a["start"])
    name = SERVICES[a["service"]][0]
    head = "☀️ Доброго ранку! Сьогодні у вас запис." if kind == "morning" else "⏰ Нагадуємо про запис сьогодні."
    return (
        f"{head}\n\n"
        f"🕒 {st:%H:%M}, {name}\n"
        f"👤 Майстер: {MASTERS[a['master']]}\n"
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


async def notify_client(bot, a, text: str, sms_text: str) -> None:
    if a["tg_id"]:  # записи з сайту без прив'язки до Telegram отримують лише SMS
        try:
            await bot.send_message(a["tg_id"], text)
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
    src = "сайт" if a["source"] == "web" else "Telegram-бот"
    start = datetime.fromisoformat(a["start"])
    await notify_admins(
        bot,
        f"🆕 Новий запис ({src})\n{a['name']} · {a['phone']}\n"
        f"{SERVICES[a['service']][0]}, {MASTERS[a['master']]}\n{fmt(start)}",
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
    for mid, name in MASTERS.items():
        b.button(text=name, callback_data=f"m:{sid}:{mid}")
    b.button(text="‹ Назад", callback_data="book")
    b.adjust(1)
    return b.as_markup()


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
async def cmd_start(m: Message, state: FSMContext):
    await state.clear()
    await m.answer(
        f"Вітаємо в «{SHOP_NAME}»!\n\nТут можна записатися без дзвінків за хвилину.",
        reply_markup=kb_main(),
    )


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
        lines.append(f"• {fmt(datetime.fromisoformat(r['start']))}, {SERVICES[r['service']][0]}, {MASTERS[r['master']]}")
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
            f"{st:%H:%M} · {r['name']} · {r['phone']}\n   {SERVICES[r['service']][0]}, {MASTERS[r['master']]} ({src})"
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


# ---------- Меню та кроки запису ----------
@router.callback_query(F.data == "home")
async def cb_home(cb: CallbackQuery):
    await show(cb, f"«{SHOP_NAME}»\n\nОберіть дію:", kb_main())


@router.callback_query(F.data == "info")
async def cb_info(cb: CallbackQuery):
    lines = ["Ціни:\n"]
    for name, mins, price in SERVICES.values():
        lines.append(f"• {name}, {mins} хв: {price} ₴")
    lines.append(f"\n📍 {ADDRESS}")
    lines.append(f"🕒 Щодня {OPEN_HOUR}:00–{OPEN_HOUR + SLOTS // 2}:00")
    b = InlineKeyboardBuilder()
    b.button(text="Записатися", callback_data="book")
    b.button(text="‹ Назад", callback_data="home")
    b.adjust(1)
    await show(cb, "\n".join(lines), b.as_markup())


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
    if sid not in SERVICES or mid not in MASTERS:
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
        f"{name}, {MASTERS[mid]}\n📅 {fmt(slot_dt(day, i))}\n💰 {price} ₴\n\n"
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
                    SELECT r.id AS rid, r.kind, a.tg_id, a.phone, a.service, a.master, a.start
                    FROM reminders r JOIN appts a ON a.id = r.appt_id
                    WHERE r.sent = 0 AND r.send_at <= ? AND a.status = 'booked'
                    """,
                    (current,),
                ).fetchall()
            for r in rows:
                if datetime.fromisoformat(r["start"]) > now():
                    await notify_client(bot, r, text_reminder(r["kind"], r), sms_reminder(r))
                with closing(db()) as c:
                    c.execute("UPDATE reminders SET sent=1 WHERE id=?", (r["rid"],))
                    c.commit()
        except Exception:
            logging.exception("Помилка в циклі нагадувань")
        await asyncio.sleep(30)


# ---------- Сайт і API ----------
RATE: dict = {}


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
        resp.headers["Access-Control-Allow-Headers"] = "Content-Type"
        resp.headers["Access-Control-Allow-Methods"] = "GET,POST,OPTIONS"
    return resp


async def api_config(request):
    return web.json_response(
        {
            "ok": True,
            "shop": SHOP_NAME,
            "address": ADDRESS,
            "bot": BOT_USERNAME,
            "services": [{"id": k, "name": v[0], "min": v[1], "price": v[2]} for k, v in SERVICES.items()],
            "masters": [{"id": k, "name": v} for k, v in MASTERS.items()],
        }
    )


async def api_days(request):
    sid, mid = request.query.get("service"), request.query.get("master")
    if sid not in SERVICES or mid not in MASTERS:
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
    if sid not in SERVICES or mid not in MASTERS or not day:
        return jerr("Невірні параметри.")
    return web.json_response(
        {"ok": True, "slots": [{"i": i, "label": slot_label(i)} for i in free_slots(day, mid, sid)]}
    )


async def api_book(request):
    if rate_limited(request.remote or "?"):
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
    if sid not in SERVICES or mid not in MASTERS or not day or not isinstance(slot, int) or isinstance(slot, bool):
        return jerr("Невірні параметри запису.")
    if len(name) < 2:
        return jerr("Вкажіть ім'я.")
    if not phone:
        return jerr("Вкажіть український номер у форматі 0501234567.")
    try:
        appt = await create_appointment(
            name=name, phone=phone, sid=sid, mid=mid, day=day, slot=slot, tg_id=None, source="web"
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
            "master": MASTERS[mid],
            "price": s[2],
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
ADMIN_STATUS = {"booked": "Записан", "done": "Прийшов", "cancelled": "Скасовано"}


def admin_ok(request) -> bool:
    if not ADMIN_TOKEN:
        return False
    return request.headers.get("X-Admin-Token", "") == ADMIN_TOKEN or request.query.get("token", "") == ADMIN_TOKEN


async def admin_day(request):
    if not admin_ok(request):
        return web.json_response({"ok": False, "error": "Немає доступу"}, status=403)
    try:
        day = date.fromisoformat(request.query.get("date", ""))
    except ValueError:
        return jerr("Невірна дата.")
    with closing(db()) as c:
        rows = c.execute(
            "SELECT * FROM appts WHERE substr(start,1,10)=? ORDER BY start", (day.isoformat(),)
        ).fetchall()
    items = []
    for r in rows:
        st = datetime.fromisoformat(r["start"])
        svc = SERVICES.get(r["service"], ("?", 0, 0))
        items.append(
            {
                "id": r["id"],
                "time": f"{st:%H:%M}",
                "name": r["name"],
                "phone": r["phone"],
                "service": svc[0],
                "master": MASTERS.get(r["master"], r["master"]),
                "price": svc[2],
                "status": r["status"],
                "units": units(r["service"]) if r["service"] in SERVICES else 1,
                "source": "сайт" if r["source"] == "web" else "бот",
            }
        )
    active = [i for i in items if i["status"] != "cancelled"]
    revenue = sum(i["price"] for i in items if i["status"] == "done")
    used = sum(i["units"] for i in active)
    return web.json_response(
        {
            "ok": True,
            "items": items,
            "stats": {
                "count": len(active),
                "revenue": revenue,
                "load": round(used / (SLOTS * len(MASTERS)) * 100),
            },
        }
    )


async def admin_status(request):
    if not admin_ok(request):
        return web.json_response({"ok": False, "error": "Немає доступу"}, status=403)
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
        c.execute("UPDATE appts SET status=? WHERE id=?", (status, appt_id))
        c.commit()
    if a["status"] != status:
        label = ADMIN_STATUS[status]
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
        return web.json_response({"ok": False, "error": "Немає доступу"}, status=403)
    with closing(db()) as c:
        rows = c.execute("SELECT name, phone, service, start, status FROM appts").fetchall()
    today = now().date()
    clients: dict = {}
    for r in rows:
        p = r["phone"] or "?"
        cinfo = clients.setdefault(p, {"name": r["name"], "phone": p, "visits": 0, "spent": 0, "last": None, "upcoming": False})
        if r["name"]:
            cinfo["name"] = r["name"]
        if r["status"] == "done":
            cinfo["visits"] += 1
            cinfo["spent"] += SERVICES.get(r["service"], ("", 0, 0))[2]
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

def build_app(bot) -> web.Application:
    app = web.Application(middlewares=[cors])
    app["bot"] = bot
    app.router.add_get("/", index)
    app.router.add_get("/healthz", lambda r: web.Response(text="ok"))
    app.router.add_get("/admin", admin_page)
    app.router.add_get("/admin/api/day", admin_day)
    app.router.add_get("/admin/api/clients", admin_clients)
    app.router.add_post("/admin/api/status", admin_status)
    app.router.add_get("/api/config", api_config)
    app.router.add_get("/api/days", api_days)
    app.router.add_get("/api/slots", api_slots)
    app.router.add_post("/api/book", api_book)
    app.router.add_route("OPTIONS", "/api/{tail:.*}", lambda r: web.Response())
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
