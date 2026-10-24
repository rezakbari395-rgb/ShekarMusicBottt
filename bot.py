import asyncio
import logging
import math
import os
import re
import secrets
import shutil
import sqlite3
import subprocess
import tempfile
import time
from functools import wraps
from pathlib import Path

import yt_dlp
from dotenv import load_dotenv
from telegram import (
    BotCommand,
    BotCommandScopeAllGroupChats,
    BotCommandScopeAllPrivateChats,
    ForceReply,
    InlineKeyboardButton as Btn,
    InlineKeyboardMarkup as Markup,
    Update,
)
from telegram.constants import ChatAction, ChatType, ParseMode
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    ChatMemberHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

try:
    import jdatetime  # تاریخ شمسی
except ImportError:  # pragma: no cover
    jdatetime = None

_ENV_FILE = Path(__file__).resolve().with_name(".env")
# utf-8-sig: علامت نامرئی (BOM) که Notepad اول فایل می‌ذاره مشکلی درست نکنه
load_dotenv(_ENV_FILE, encoding="utf-8-sig")

# ============================== تنظیمات ==============================
if "BOT_TOKEN" not in os.environ:
    raise SystemExit(
        "\n❌ BOT_TOKEN پیدا نشد.\n"
        f"فایل .env باید دقیقاً اینجا باشه: {_ENV_FILE}\n"
        "و خط اولش این شکلی باشه: BOT_TOKEN=توکن_ربات\n"
        "(اسم فایل نباید .env.txt یا .env.example باشه)\n"
    )
BOT_TOKEN = os.environ["BOT_TOKEN"].strip()


def _int_set(s: str) -> set[int]:
    out = set()
    for x in re.split(r"[,\s]+", s or ""):
        if x.strip().lstrip("-").isdigit():
            out.add(int(x))
    return out


OWNER_IDS = _int_set(os.getenv("OWNER_IDS", ""))
SUPPORT_USERNAME = os.getenv("SUPPORT_USERNAME", "").strip().lstrip("@")
PLANS_TEXT = os.getenv(
    "PLANS_TEXT", "برای خرید اشتراک با پشتیبانی در ارتباط باش."
).replace("\\n", "\n")
TRIAL_DAYS = int(os.getenv("TRIAL_DAYS", "0") or 0)
MAX_DURATION = int(os.getenv("MAX_DURATION_SECONDS", "900"))
MAX_FILE_MB = 49
CONCURRENT_DOWNLOADS = int(os.getenv("CONCURRENT_DOWNLOADS", "3"))
PV_COOLDOWN = int(os.getenv("USER_COOLDOWN_SECONDS", "3"))
DB_PATH = os.getenv("DB_PATH", "music.db")
COOKIES_FILE = os.getenv("COOKIES_FILE", "").strip()

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
# جلوگیری از چاپ توکن در لاگ‌ها
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("httpcore").setLevel(logging.WARNING)
log = logging.getLogger("musicbot")

URL_RE = re.compile(r"https?://\S+")
REPLY_PREFIX = "🔎 اسم آهنگ"
PAGE_RES = 5
PAGE_LIST = 6
DL_SEM = asyncio.Semaphore(CONCURRENT_DOWNLOADS)
ACTIVE: set[int] = set()  # کاربرهایی که الان درخواست در حال انجام دارن
SEARCHES: dict[str, dict] = {}
LAST_REQ: dict[tuple[int, int], float] = {}


# ============================== دیتابیس ==============================
def db(sql: str, params=(), mode: str = "none"):
    con = sqlite3.connect(DB_PATH, timeout=15)
    try:
        cur = con.execute(sql, params)
        if mode == "one":
            res = cur.fetchone()
        elif mode == "all":
            res = cur.fetchall()
        elif mode == "rc":
            res = cur.rowcount
        else:
            res = None
        con.commit()
        return res
    finally:
        con.close()


def db_init() -> None:
    con = sqlite3.connect(DB_PATH, timeout=15)
    try:
        con.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                name TEXT,
                first_seen INTEGER,
                quality INTEGER DEFAULT 192,
                banned INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS groups (
                chat_id INTEGER PRIMARY KEY,
                title TEXT,
                added INTEGER,
                mode TEXT DEFAULT 'all',
                cooldown INTEGER DEFAULT 5,
                buttons INTEGER DEFAULT 1,
                clean INTEGER DEFAULT 1
            );
            CREATE TABLE IF NOT EXISTS subs (
                subject_id INTEGER PRIMARY KEY,
                kind TEXT,
                expires_at INTEGER,
                notified INTEGER DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS licenses (
                key TEXT PRIMARY KEY,
                days INTEGER,
                scope TEXT DEFAULT 'any',
                created_at INTEGER,
                created_by INTEGER,
                used_by INTEGER,
                used_subject INTEGER,
                used_at INTEGER
            );
            CREATE TABLE IF NOT EXISTS meta (
                video_id TEXT PRIMARY KEY,
                title TEXT,
                artist TEXT,
                duration INTEGER
            );
            CREATE TABLE IF NOT EXISTS files (
                video_id TEXT,
                quality INTEGER,
                file_id TEXT NOT NULL,
                PRIMARY KEY (video_id, quality)
            );
            CREATE TABLE IF NOT EXISTS favs (
                user_id INTEGER,
                video_id TEXT,
                added INTEGER,
                PRIMARY KEY (user_id, video_id)
            );
            CREATE TABLE IF NOT EXISTS history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                chat_id INTEGER,
                video_id TEXT,
                ts INTEGER
            );
            CREATE INDEX IF NOT EXISTS idx_hist_user ON history(user_id);
            CREATE INDEX IF NOT EXISTS idx_hist_chat ON history(chat_id);
            """
        )
        con.commit()
    finally:
        con.close()


# ---- کاربرها ----
def touch_user(u) -> bool:
    """ثبت کاربر. اگه برای اولین بار دیده شد True برمی‌گردونه."""
    name = (u.full_name or "")[:64]
    new = (
        db(
            "INSERT OR IGNORE INTO users(user_id, name, first_seen) VALUES (?,?,?)",
            (u.id, name, int(time.time())),
            "rc",
        )
        == 1
    )
    if not new:
        db("UPDATE users SET name=? WHERE user_id=?", (name, u.id))
    return new


def is_banned(uid: int) -> bool:
    row = db("SELECT banned FROM users WHERE user_id=?", (uid,), "one")
    return bool(row and row[0])


def get_quality(uid: int) -> int:
    row = db("SELECT quality FROM users WHERE user_id=?", (uid,), "one")
    return int(row[0]) if row and row[0] else 192


# ---- گروه‌ها ----
GROUP_DEFAULTS = {"mode": "all", "cooldown": 5, "buttons": 1, "clean": 1}
GROUP_FIELDS = {"mode", "cooldown", "buttons", "clean"}


def touch_group(chat) -> None:
    db(
        "INSERT OR IGNORE INTO groups(chat_id, title, added) VALUES (?,?,?)",
        (chat.id, chat.title or "", int(time.time())),
    )
    db("UPDATE groups SET title=? WHERE chat_id=?", (chat.title or "", chat.id))


def get_group(chat_id: int) -> dict:
    row = db(
        "SELECT mode, cooldown, buttons, clean FROM groups WHERE chat_id=?",
        (chat_id,),
        "one",
    )
    if not row:
        return dict(GROUP_DEFAULTS)
    return {"mode": row[0], "cooldown": row[1], "buttons": row[2], "clean": row[3]}


def set_group(chat_id: int, field: str, value) -> None:
    if field not in GROUP_FIELDS:
        raise ValueError(field)
    db(f"UPDATE groups SET {field}=? WHERE chat_id=?", (value, chat_id))


# ---- اشتراک و لایسنس ----
def sub_expiry(subject_id: int):
    row = db("SELECT expires_at FROM subs WHERE subject_id=?", (subject_id,), "one")
    if row and row[0] and row[0] > time.time():
        return int(row[0])
    return None


def add_days(subject_id: int, kind: str, days: int) -> int:
    now = int(time.time())
    row = db("SELECT expires_at FROM subs WHERE subject_id=?", (subject_id,), "one")
    base = row[0] if row and row[0] and row[0] > now else now
    new = int(base + days * 86400)
    db(
        "INSERT INTO subs(subject_id, kind, expires_at, notified) VALUES (?,?,?,0)"
        " ON CONFLICT(subject_id) DO UPDATE SET"
        " expires_at=excluded.expires_at, kind=excluded.kind, notified=0",
        (subject_id, kind, new),
    )
    return new


def revoke_sub(subject_id: int) -> None:
    db("DELETE FROM subs WHERE subject_id=?", (subject_id,))


def make_keys(days: int, count: int, scope: str, by: int) -> list[str]:
    keys = []
    for _ in range(count):
        key = "MB-" + "-".join(secrets.token_hex(2).upper() for _ in range(4))
        db(
            "INSERT INTO licenses(key, days, scope, created_at, created_by) VALUES (?,?,?,?,?)",
            (key, days, scope, int(time.time()), by),
        )
        keys.append(key)
    return keys


def redeem_key(key: str, subject_id: int, kind: str, by: int):
    """برمی‌گردونه (وضعیت، مقدار). وضعیت: ok / invalid / used / scope"""
    row = db("SELECT days, scope, used_by FROM licenses WHERE key=?", (key,), "one")
    if not row:
        return "invalid", None
    days, scope, used_by = row
    if used_by is not None:
        return "used", None
    if scope not in ("any", kind):
        return "scope", scope
    rc = db(
        "UPDATE licenses SET used_by=?, used_subject=?, used_at=? WHERE key=? AND used_by IS NULL",
        (by, subject_id, int(time.time()), key),
        "rc",
    )
    if rc != 1:
        return "used", None
    return "ok", add_days(subject_id, kind, days)


# ---- آهنگ‌ها ----
def save_meta(vid: str, title: str, artist: str, duration: int, overwrite=False):
    if overwrite:
        db(
            "INSERT INTO meta(video_id, title, artist, duration) VALUES (?,?,?,?)"
            " ON CONFLICT(video_id) DO UPDATE SET"
            " title=excluded.title, artist=excluded.artist, duration=excluded.duration",
            (vid, title, artist, duration),
        )
    else:
        db(
            "INSERT OR IGNORE INTO meta(video_id, title, artist, duration) VALUES (?,?,?,?)",
            (vid, title, artist, duration),
        )


def get_meta(vid: str):
    row = db(
        "SELECT title, artist, duration FROM meta WHERE video_id=?", (vid,), "one"
    )
    if not row:
        return None
    return {"title": row[0] or "", "artist": row[1] or "", "duration": row[2] or 0}


def file_get(vid: str, quality: int):
    row = db(
        "SELECT file_id FROM files WHERE video_id=? AND quality=?",
        (vid, quality),
        "one",
    )
    return row[0] if row else None


def file_put(vid: str, quality: int, file_id: str) -> None:
    db(
        "INSERT OR REPLACE INTO files(video_id, quality, file_id) VALUES (?,?,?)",
        (vid, quality, file_id),
    )


def add_history(uid: int, chat_id: int, vid: str) -> None:
    db(
        "INSERT INTO history(user_id, chat_id, video_id, ts) VALUES (?,?,?,?)",
        (uid, chat_id, vid, int(time.time())),
    )


def fav_toggle(uid: int, vid: str) -> bool:
    """اگه اضافه شد True، اگه حذف شد False."""
    if db("DELETE FROM favs WHERE user_id=? AND video_id=?", (uid, vid), "rc") == 1:
        return False
    db(
        "INSERT OR IGNORE INTO favs(user_id, video_id, added) VALUES (?,?,?)",
        (uid, vid, int(time.time())),
    )
    return True


def list_rows(kind: str, uid: int, chat_id: int, page: int):
    off = page * PAGE_LIST
    base = "SELECT m.video_id, m.title, m.artist, m.duration FROM "
    if kind == "favs":
        sql = (
            base + "favs f JOIN meta m ON m.video_id=f.video_id WHERE f.user_id=?"
            " ORDER BY f.added DESC LIMIT ? OFFSET ?"
        )
        params = (uid, PAGE_LIST + 1, off)
    elif kind == "hist":
        sql = (
            base + "history h JOIN meta m ON m.video_id=h.video_id WHERE h.user_id=?"
            " GROUP BY m.video_id ORDER BY MAX(h.ts) DESC LIMIT ? OFFSET ?"
        )
        params = (uid, PAGE_LIST + 1, off)
    elif kind == "gtop":
        sql = (
            base + "history h JOIN meta m ON m.video_id=h.video_id WHERE h.chat_id=?"
            " GROUP BY m.video_id ORDER BY COUNT(*) DESC LIMIT ? OFFSET ?"
        )
        params = (chat_id, PAGE_LIST + 1, off)
    else:  # top
        sql = (
            base + "history h JOIN meta m ON m.video_id=h.video_id"
            " GROUP BY m.video_id ORDER BY COUNT(*) DESC LIMIT ? OFFSET ?"
        )
        params = (PAGE_LIST + 1, off)
    rows = db(sql, params, "all")
    return rows[:PAGE_LIST], len(rows) > PAGE_LIST


# ============================== ابزارهای کمکی ==============================
def fmt_duration(sec: int) -> str:
    if not sec:
        return "—"
    m, s = divmod(int(sec), 60)
    return f"{m}:{s:02d}"


def fdate(ts: int) -> str:
    if jdatetime:
        return jdatetime.datetime.fromtimestamp(ts).strftime("%Y/%m/%d")
    return time.strftime("%Y-%m-%d", time.localtime(ts))


def days_left(exp: int) -> int:
    return max(1, math.ceil((exp - time.time()) / 86400))


def is_group(chat) -> bool:
    return chat.type in (ChatType.GROUP, ChatType.SUPERGROUP)


def buy_btn():
    if SUPPORT_USERNAME:
        return Btn("🛒 خرید اشتراک", url=f"https://t.me/{SUPPORT_USERNAME}")
    return None


def sub_line(subject_id: int, group: bool = False) -> str:
    if not group and subject_id in OWNER_IDS:
        return "👑 مالک ربات (دسترسی نامحدود)"
    exp = sub_expiry(subject_id)
    if exp:
        return f"💎 اشتراک: ✅ فعال تا {fdate(exp)} ({days_left(exp)} روز مانده)"
    return "💎 اشتراک: ❌ غیرفعال"


async def is_admin(ctx, chat_id: int, uid: int) -> bool:
    if uid in OWNER_IDS:
        return True
    try:
        m = await ctx.bot.get_chat_member(chat_id, uid)
        return m.status in ("administrator", "creator")
    except TelegramError:
        return False


async def check_access(ctx, chat, user):
    """(مجاز بودن، دلیل). دلیل: ok / banned / nosub / adminonly"""
    if user.id in OWNER_IDS:
        return True, "ok"
    if is_banned(user.id):
        return False, "banned"
    if not is_group(chat):
        return (True, "ok") if sub_expiry(user.id) else (False, "nosub")
    if not sub_expiry(chat.id):
        return False, "nosub"
    if get_group(chat.id)["mode"] == "admins" and not await is_admin(
        ctx, chat.id, user.id
    ):
        return False, "adminonly"
    return True, "ok"


def deny_text(reason: str, chat) -> str:
    if reason == "banned":
        return "⛔ دسترسی شما به ربات مسدوده."
    if reason == "adminonly":
        return "🔒 تو این گروه فقط ادمین‌ها می‌تونن از ربات استفاده کنن."
    if is_group(chat):
        return "⛔ اشتراک این گروه فعال نیست."
    return "⛔ اشتراک شما فعال نیست."


async def deny(msg, reason: str, chat) -> None:
    text = deny_text(reason, chat)
    rows = []
    if reason == "nosub":
        if is_group(chat):
            text += "\nادمین گروه می‌تونه با /redeem کد لایسنس رو فعال کنه."
        else:
            rows.append([Btn("🔑 فعال‌سازی لایسنس", callback_data="m:key")])
        b = buy_btn()
        if b:
            rows.append([b])
    await msg.reply_text(text, reply_markup=Markup(rows) if rows else None)


def cooldown_left(chat, user) -> int:
    if user.id in OWNER_IDS:
        return 0
    cd = get_group(chat.id)["cooldown"] if is_group(chat) else PV_COOLDOWN
    now = time.time()
    if len(LAST_REQ) > 5000:
        LAST_REQ.clear()
    key = (chat.id, user.id)
    left = cd - (now - LAST_REQ.get(key, 0))
    if left > 0:
        return math.ceil(left)
    LAST_REQ[key] = now
    return 0


async def show(q, ctx, text, markup=None, parse_mode=None):
    """پیام فعلی رو ویرایش می‌کنه؛ اگه پیام آهنگ بود، پیام جدید می‌فرسته."""
    m = q.message
    if getattr(m, "text", None) is not None:
        try:
            await q.edit_message_text(text, reply_markup=markup, parse_mode=parse_mode)
            return
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return
            log.warning("edit failed: %s", e)
    await ctx.bot.send_message(
        m.chat_id, text, reply_markup=markup, parse_mode=parse_mode
    )


# ============================== جستجو و دانلود (yt-dlp) ==============================
def _base_opts() -> dict:
    o = {"quiet": True, "no_warnings": True, "noplaylist": True}
    if COOKIES_FILE and os.path.isfile(COOKIES_FILE):
        o["cookiefile"] = COOKIES_FILE
    return o


def _entry(e) -> dict:
    return {
        "id": e["id"],
        "title": e.get("title") or "Unknown",
        "duration": int(e.get("duration") or 0),
        "uploader": e.get("uploader") or e.get("channel") or "",
    }


def _ok_len(r: dict) -> bool:
    return r["duration"] == 0 or r["duration"] <= MAX_DURATION


def _search_sync(query: str, n: int = 10):
    opts = {**_base_opts(), "extract_flat": True, "skip_download": True}
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(f"ytsearch{n}:{query}", download=False)
    res = [_entry(e) for e in (info.get("entries") or []) if e and e.get("id")]
    return [r for r in res if _ok_len(r)]


def _similar_sync(vid: str, title: str, artist: str, n: int = 10):
    res = []
    try:
        opts = {
            **_base_opts(),
            "noplaylist": False,
            "extract_flat": True,
            "skip_download": True,
            "playlistend": n + 3,
        }
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(
                f"https://www.youtube.com/watch?v={vid}&list=RD{vid}", download=False
            )
        res = [
            _entry(e)
            for e in (info.get("entries") or [])
            if e and e.get("id") and e["id"] != vid
        ]
    except Exception as e:  # noqa: BLE001
        log.warning("mix failed: %s", e)
    if len(res) < 3:
        q = (artist or title or "").strip()
        if q:
            seen = {r["id"] for r in res} | {vid}
            try:
                res += [r for r in _search_sync(f"{q} mix", n + 3) if r["id"] not in seen]
            except Exception as e:  # noqa: BLE001
                log.warning("similar search failed: %s", e)
    return [r for r in res if _ok_len(r)][:n]


def _info_sync(url: str):
    with yt_dlp.YoutubeDL({**_base_opts(), "skip_download": True}) as ydl:
        return ydl.extract_info(url, download=False)


def _clear_dir(workdir: str) -> None:
    for f in Path(workdir).glob("*"):
        try:
            f.unlink()
        except OSError:
            pass


def _download_sync(vid: str, workdir: str, quality: int):
    """چند روش پشت‌سرهم امتحان می‌کنه تا یکی جواب بده."""
    url = f"https://www.youtube.com/watch?v={vid}"
    common = {
        **_base_opts(),
        "outtmpl": os.path.join(workdir, "%(id)s.%(ext)s"),
        "writethumbnail": True,
        "retries": 5,
        "fragment_retries": 5,
        "socket_timeout": 30,
        # فقط استخراج mp3؛ کاور جداگانه و بدون ایجاد خطا آماده می‌شه
        "postprocessors": [
            {
                "key": "FFmpegExtractAudio",
                "preferredcodec": "mp3",
                "preferredquality": str(quality),
            }
        ],
    }
    attempts = [
        {"format": "bestaudio/best"},
        {
            "format": "bestaudio*/best",
            "extractor_args": {"youtube": {"player_client": ["tv", "web_safari", "mweb"]}},
        },
        {"format": "best", "writethumbnail": False},
    ]
    last_err = None
    for i, extra in enumerate(attempts, 1):
        _clear_dir(workdir)
        try:
            with yt_dlp.YoutubeDL({**common, **extra}) as ydl:
                info = ydl.extract_info(url, download=True)
            if next(Path(workdir).glob("*.mp3"), None):
                return info
            last_err = RuntimeError("mp3 file was not produced")
        except Exception as e:  # noqa: BLE001
            last_err = e
            log.warning("download attempt %d/%d failed for %s: %s", i, len(attempts), vid, e)
    raise last_err


def _make_thumb(workdir: str):
    """کاور رو کوچیک و jpg می‌کنه؛ اگه نشد None (و دانلود ادامه پیدا می‌کنه)."""
    src = None
    for ext in ("jpg", "jpeg", "png", "webp"):
        src = next(Path(workdir).glob(f"*.{ext}"), None)
        if src:
            break
    if not src or not shutil.which("ffmpeg"):
        return None
    out = Path(workdir) / "cover_small.jpg"
    try:
        subprocess.run(
            ["ffmpeg", "-y", "-loglevel", "error", "-i", str(src),
             "-vf", "scale=320:-2", "-q:v", "5", str(out)],
            check=True, timeout=30,
        )
        if out.exists() and 0 < out.stat().st_size <= 200 * 1024:
            return out
    except Exception as e:  # noqa: BLE001
        log.warning("thumbnail skipped: %s", e)
    return None


def friendly_error(exc: Exception) -> str:
    m = str(exc).lower()
    if "ffmpeg" in m or "ffprobe" in m:
        return "❌ ffmpeg روی سرور نصب نیست یا پیدا نمی‌شه."
    if "confirm you" in m and "bot" in m or "sign in to confirm" in m:
        return "🤖 یوتیوب این درخواست رو رد کرد (نیاز به کوکی). بعداً دوباره امتحان کن."
    if "age" in m and ("restrict" in m or "confirm your age" in m or "inappropriate" in m):
        return "🔞 این آهنگ محدودیت سنی داره و قابل دانلود نیست."
    if "private" in m or "members-only" in m or "premium" in m:
        return "🔒 این ویدیو خصوصی یا مخصوص اعضاست."
    if "not available" in m or "unavailable" in m or "blocked" in m or "country" in m:
        return "🌍 این آهنگ در دسترس نیست (حذف‌شده یا محدودیت منطقه‌ای)."
    if "live" in m and "stream" in m:
        return "📡 پخش زنده قابل دانلود نیست."
    if "timed out" in m or "timeout" in m or "connection" in m:
        return "🌐 مشکل اتصال به یوتیوب. چند لحظه بعد دوباره امتحان کن."
    return "❌ خطا در دانلود این آهنگ. یه نتیجه‌ی دیگه رو امتحان کن."


# ============================== نتایج جستجو (صفحه‌بندی) ==============================
def new_search(uid: int, query: str, results: list, kind: str = "search") -> str:
    now = time.time()
    for k in [k for k, v in SEARCHES.items() if now - v["ts"] > 3600]:
        SEARCHES.pop(k, None)
    if len(SEARCHES) > 1000:
        for k in sorted(SEARCHES, key=lambda x: SEARCHES[x]["ts"])[:200]:
            SEARCHES.pop(k, None)
    for r in results:
        save_meta(r["id"], r["title"], r["uploader"], r["duration"])
    sid = secrets.token_hex(3)
    SEARCHES[sid] = {"uid": uid, "q": query, "results": results, "kind": kind, "ts": now}
    return sid


def render_search(sid: str, page: int):
    s = SEARCHES.get(sid)
    if not s:
        return None
    res = s["results"]
    pages = max(1, math.ceil(len(res) / PAGE_RES))
    page = max(0, min(page, pages - 1))
    chunk = res[page * PAGE_RES : (page + 1) * PAGE_RES]
    if s["kind"] == "similar":
        head = f"🎼 آهنگ‌های مشابه «{s['q'][:40]}»"
    else:
        head = f"🔎 نتایج «{s['q'][:40]}»"
    lines = [head, ""]
    for i, r in enumerate(chunk, 1):
        lines.append(
            f"{i}. {r['title'][:60]}\n    👤 {(r['uploader'] or '—')[:30]}   ⏱ {fmt_duration(r['duration'])}"
        )
    lines.append("\nشماره‌ی آهنگ رو انتخاب کن 👇")
    rows = [
        [
            Btn(str(i), callback_data=f"dl:{r['id']}:{s['uid']}")
            for i, r in enumerate(chunk, 1)
        ]
    ]
    if pages > 1:
        nav = []
        if page > 0:
            nav.append(Btn("◀️ قبلی", callback_data=f"pg:{sid}:{page - 1}"))
        nav.append(Btn(f"{page + 1}/{pages}", callback_data="noop"))
        if page < pages - 1:
            nav.append(Btn("بعدی ▶️", callback_data=f"pg:{sid}:{page + 1}"))
        rows.append(nav)
    rows.append(
        [
            Btn("🔄 جستجوی دوباره", callback_data="r"),
            Btn("❌ بستن", callback_data=f"x:{s['uid']}"),
        ]
    )
    return "\n".join(lines), Markup(rows)


def track_markup(vid: str, group: bool) -> Markup:
    row2 = [Btn("🔎 جستجوی دوباره", callback_data="r")]
    if group:
        row2.append(Btn("🔥 تاپ گروه", callback_data="ls:gtop:0"))
    else:
        row2.append(Btn("🏠 منو", callback_data="m:home"))
    return Markup(
        [
            [
                Btn("❤️ علاقه‌مندی", callback_data=f"f:{vid}"),
                Btn("🎼 مشابه", callback_data=f"s:{vid}"),
            ],
            row2,
        ]
    )


# ============================== ویوها (متن و دکمه‌ها) ==============================
LIST_TITLES = {
    "favs": "❤️ علاقه‌مندی‌های تو",
    "hist": "🕘 تاریخچه‌ی آهنگ‌های تو",
    "top": "🔥 پرطرفدارترین آهنگ‌ها",
    "gtop": "🔥 پرطرفدارهای این گروه",
}


def list_view(kind: str, uid: int, chat_id: int, page: int, group: bool):
    rows, has_next = list_rows(kind, uid, chat_id, page)
    title = LIST_TITLES.get(kind, "لیست")
    owner = uid if kind in ("favs", "hist") else 0  # 0 یعنی همه می‌تونن بزنن
    if not rows:
        text = f"{title}\n\nهنوز چیزی اینجا نیست."
        if kind == "favs":
            text += "\nزیر هر آهنگ روی ❤️ بزن تا اینجا ذخیره بشه."
        nums = []
    else:
        lines = [title, ""]
        for i, (vid, t, a, d) in enumerate(rows, 1):
            lines.append(
                f"{i}. {(t or 'Unknown')[:60]}\n    👤 {(a or '—')[:30]}   ⏱ {fmt_duration(d)}"
            )
        lines.append("\nشماره‌ی آهنگ رو انتخاب کن 👇")
        text = "\n".join(lines)
        nums = [
            Btn(str(i), callback_data=f"dl:{vid}:{owner}")
            for i, (vid, *_rest) in enumerate(rows, 1)
        ]
    kb = []
    if nums:
        kb.append(nums)
    nav = []
    if page > 0:
        nav.append(Btn("◀️ قبلی", callback_data=f"ls:{kind}:{page - 1}"))
    if has_next:
        nav.append(Btn("بعدی ▶️", callback_data=f"ls:{kind}:{page + 1}"))
    if nav:
        kb.append(nav)
    kb.append(
        [Btn("❌ بستن", callback_data="x:0")]
        if group
        else [Btn("🏠 منو", callback_data="m:home")]
    )
    return text, Markup(kb)


def main_menu(user_id: int) -> Markup:
    rows = [
        [
            Btn("🔎 جستجوی آهنگ", callback_data="m:search"),
            Btn("🔥 پرطرفدارها", callback_data="ls:top:0"),
        ],
        [
            Btn("❤️ علاقه‌مندی‌ها", callback_data="ls:favs:0"),
            Btn("🕘 تاریخچه", callback_data="ls:hist:0"),
        ],
        [
            Btn("👤 پروفایل و اشتراک", callback_data="m:sub"),
            Btn("⚙️ تنظیمات", callback_data="m:set"),
        ],
    ]
    last = [Btn("📖 راهنما", callback_data="m:help")]
    if SUPPORT_USERNAME:
        last.append(Btn("💬 پشتیبانی", url=f"https://t.me/{SUPPORT_USERNAME}"))
    rows.append(last)
    return Markup(rows)


def home_text(user) -> str:
    return (
        f"🎵 سلام {user.first_name}!\n\n"
        "اسم آهنگ یا لینک یوتیوب رو بفرست تا با کیفیت بالا برات بفرستم.\n\n"
        f"{sub_line(user.id)}\n\n"
        "از منوی زیر شروع کن 👇"
    )


def profile_view(user):
    n_dl = db("SELECT COUNT(*) FROM history WHERE user_id=?", (user.id,), "one")[0]
    n_fav = db("SELECT COUNT(*) FROM favs WHERE user_id=?", (user.id,), "one")[0]
    lines = [
        "👤 پروفایل و اشتراک",
        "",
        f"نام: {user.full_name}",
        f"آیدی عددی: {user.id}",
        sub_line(user.id),
        f"🎧 تعداد دریافت: {n_dl}",
        f"❤️ علاقه‌مندی‌ها: {n_fav}",
        f"🎚 کیفیت: {get_quality(user.id)}kbps",
    ]
    if not sub_expiry(user.id) and user.id not in OWNER_IDS:
        lines += ["", "━━━━━━━━━━", PLANS_TEXT]
    rows = [[Btn("🔑 فعال‌سازی لایسنس", callback_data="m:key")]]
    b = buy_btn()
    if b:
        rows.append([b])
    rows.append([Btn("🏠 منو", callback_data="m:home")])
    return "\n".join(lines), Markup(rows)


def settings_view(uid: int):
    q = get_quality(uid)
    text = (
        "⚙️ تنظیمات\n\n"
        f"🎚 کیفیت صدا: {q}kbps\n"
        "کیفیت بالاتر یعنی صدای بهتر ولی حجم بیشتر."
    )
    rows = [
        [
            Btn(("✅ " if q == x else "") + f"{x}kbps", callback_data=f"st:q:{x}")
            for x in (128, 192, 320)
        ],
        [Btn("🏠 منو", callback_data="m:home")],
    ]
    return text, Markup(rows)


HELP_PV = (
    "📖 راهنما\n\n"
    "• اسم آهنگ یا لینک یوتیوب رو بفرست.\n"
    "• زیر هر آهنگ: ❤️ علاقه‌مندی، 🎼 مشابه، 🔎 جستجوی دوباره.\n"
    "• /top پرطرفدارها  •  /profile پروفایل  •  /redeem کد فعال‌سازی لایسنس\n\n"
    "🔹 برای گروه: ربات رو به گروه اضافه کن (بهتره ادمین باشه)، ادمین گروه "
    "/redeem کد رو بزنه، بعد همه با /play اسم آهنگ آهنگ بگیرن. "
    "تنظیمات گروه با /panel."
)

HELP_GROUP = (
    "📖 راهنمای گروه\n\n"
    "• /play اسم آهنگ (یا لینک یوتیوب)\n"
    "• /top پرطرفدارهای گروه\n"
    "• /panel پنل مدیریت (فقط ادمین‌ها)\n"
    "• /redeem کد فعال‌سازی لایسنس (فقط ادمین‌ها)"
)


def group_panel(chat):
    cfg = get_group(chat.id)
    lines = [
        "⚙️ پنل مدیریت گروه",
        chat.title or "",
        "",
        sub_line(chat.id, group=True),
        f"👥 دسترسی: {'همه‌ی اعضا' if cfg['mode'] == 'all' else 'فقط ادمین‌ها'}",
        f"⏱ فاصله‌ی درخواست: {cfg['cooldown']} ثانیه",
        f"🎛 دکمه‌های زیر آهنگ: {'روشن' if cfg['buttons'] else 'خاموش'}",
        f"🧹 پاکسازی خودکار: {'روشن' if cfg['clean'] else 'خاموش'}",
    ]
    rows = [
        [
            Btn(
                f"👥 دسترسی: {'همه' if cfg['mode'] == 'all' else 'فقط ادمین‌ها'}",
                callback_data="g:mode",
            )
        ],
        [Btn(f"⏱ فاصله‌ی درخواست: {cfg['cooldown']}s", callback_data="g:cd")],
        [
            Btn(
                f"🎛 دکمه‌های زیر آهنگ: {'✅' if cfg['buttons'] else '❌'}",
                callback_data="g:btn",
            )
        ],
        [
            Btn(
                f"🧹 پاکسازی خودکار: {'✅' if cfg['clean'] else '❌'}",
                callback_data="g:clean",
            )
        ],
        [
            Btn("🔥 پرطرفدارهای گروه", callback_data="ls:gtop:0"),
            Btn("📊 آمار گروه", callback_data="g:stats"),
        ],
        [Btn("🔑 فعال‌سازی / تمدید لایسنس", callback_data="g:key")],
    ]
    b = buy_btn()
    if b:
        rows.append([b])
    rows.append([Btn("❌ بستن", callback_data="x:0")])
    return "\n".join(lines), Markup(rows)


def group_stats_text(chat_id: int) -> str:
    now = int(time.time())
    total = db("SELECT COUNT(*) FROM history WHERE chat_id=?", (chat_id,), "one")[0]
    today = db(
        "SELECT COUNT(*) FROM history WHERE chat_id=? AND ts>?", (chat_id, now - 86400), "one"
    )[0]
    users = db(
        "SELECT COUNT(DISTINCT user_id) FROM history WHERE chat_id=?", (chat_id,), "one"
    )[0]
    top = db(
        "SELECT u.name, COUNT(*) c FROM history h LEFT JOIN users u ON u.user_id=h.user_id"
        " WHERE h.chat_id=? GROUP BY h.user_id ORDER BY c DESC LIMIT 3",
        (chat_id,),
        "all",
    )
    lines = [
        "📊 آمار گروه",
        "",
        f"🎧 کل آهنگ‌های دریافت‌شده: {total}",
        f"📅 ۲۴ ساعت گذشته: {today}",
        f"👥 تعداد کاربران فعال: {users}",
    ]
    if top:
        lines += ["", "🏆 فعال‌ترین‌ها:"]
        medals = ["🥇", "🥈", "🥉"]
        for i, (name, c) in enumerate(top):
            lines.append(f"{medals[i]} {name or 'ناشناس'} — {c}")
    return "\n".join(lines)


def global_stats_text() -> str:
    now = int(time.time())

    def one(sql, p=()):
        return db(sql, p, "one")[0]

    users = one("SELECT COUNT(*) FROM users")
    groups = one("SELECT COUNT(*) FROM groups")
    sub_u = one("SELECT COUNT(*) FROM subs WHERE kind='user' AND expires_at>?", (now,))
    sub_g = one("SELECT COUNT(*) FROM subs WHERE kind='group' AND expires_at>?", (now,))
    total = one("SELECT COUNT(*) FROM history")
    today = one("SELECT COUNT(*) FROM history WHERE ts>?", (now - 86400,))
    cached = one("SELECT COUNT(*) FROM files")
    free_keys = one("SELECT COUNT(*) FROM licenses WHERE used_by IS NULL")
    return (
        "📊 آمار کل ربات\n\n"
        f"👤 کاربران: {users}\n"
        f"👥 گروه‌ها: {groups}\n"
        f"💎 اشتراک فعال کاربر: {sub_u}\n"
        f"💎 اشتراک فعال گروه: {sub_g}\n"
        f"🎧 کل دریافت‌ها: {total}\n"
        f"📅 ۲۴ ساعت گذشته: {today}\n"
        f"💾 آهنگ‌های کش‌شده: {cached}\n"
        f"🔑 لایسنس‌های استفاده‌نشده: {free_keys}"
    )


ADMIN_HELP = (
    "📣 دستورهای مالک\n\n"
    "/genkey 30 → یه لایسنس ۳۰ روزه\n"
    "/genkey 30 10 → ۱۰ تا لایسنس ۳۰ روزه\n"
    "/genkey 30 5 group → ۵ لایسنس فقط برای گروه (user / group / any)\n"
    "/grant آیدی روز → اشتراک مستقیم (آیدی گروه با منفی شروع می‌شه)\n"
    "/revoke آیدی → حذف اشتراک\n"
    "/ban آیدی  •  /unban آیدی\n"
    "/keys → لایسنس‌های استفاده‌نشده\n"
    "/stats → آمار\n"
    "/broadcast متن → ارسال پیام به همه"
)


def admin_markup() -> Markup:
    return Markup(
        [
            [
                Btn("📊 آمار", callback_data="a:stats"),
                Btn("🔑 لایسنس‌های آزاد", callback_data="a:keys"),
            ],
            [Btn("📣 راهنمای دستورها", callback_data="a:help")],
            [Btn("❌ بستن", callback_data="x:0")],
        ]
    )


# ============================== ارسال آهنگ ==============================
async def deliver(ctx, chat, user, vid: str, status, info=None) -> None:
    chat_id = chat.id
    group = is_group(chat)
    quality = get_quality(user.id)
    cfg = get_group(chat_id) if group else None
    markup = track_markup(vid, group) if (not group or cfg["buttons"]) else None
    caption = f"🎧 @{ctx.bot.username}"
    if group:
        caption = f"👤 {user.first_name}\n" + caption

    async def done(text=None):
        if status:
            try:
                await status.delete()
            except TelegramError:
                pass
        if text:
            await ctx.bot.send_message(chat_id, text)

    # ۱) از کش
    cached = file_get(vid, quality)
    meta = get_meta(vid)
    if cached and meta:
        try:
            await ctx.bot.send_audio(
                chat_id,
                cached,
                title=meta["title"],
                performer=meta["artist"],
                duration=meta["duration"],
                caption=caption,
                reply_markup=markup,
            )
            add_history(user.id, chat_id, vid)
            await done()
            return
        except TelegramError as e:
            log.warning("cached send failed: %s", e)

    if info and (info.get("duration") or 0) > MAX_DURATION:
        await done(f"⛔ آهنگ خیلی طولانیه (حداکثر {MAX_DURATION // 60} دقیقه).")
        return

    # ۲) دانلود
    async with DL_SEM:
        workdir = tempfile.mkdtemp(prefix="music_")
        try:
            if status:
                try:
                    await status.edit_text("⬇️ در حال دانلود و آماده‌سازی...")
                except TelegramError:
                    pass
            await ctx.bot.send_chat_action(chat_id, ChatAction.UPLOAD_VOICE)
            info = await asyncio.to_thread(_download_sync, vid, workdir, quality)
            if (info.get("duration") or 0) > MAX_DURATION:
                await done(f"⛔ آهنگ خیلی طولانیه (حداکثر {MAX_DURATION // 60} دقیقه).")
                return
            mp3 = next(Path(workdir).glob("*.mp3"), None)
            if not mp3:
                await done("❌ دانلود ناموفق بود.")
                return
            if mp3.stat().st_size > MAX_FILE_MB * 1024 * 1024:
                await done("⛔ حجم فایل از محدودیت تلگرام بیشتره. کیفیت رو از تنظیمات کم کن.")
                return
            thumb = await asyncio.to_thread(_make_thumb, workdir)

            title = info.get("track") or info.get("title") or "Unknown"
            artist = info.get("artist") or info.get("uploader") or ""
            duration = int(info.get("duration") or 0)

            await ctx.bot.send_chat_action(chat_id, ChatAction.UPLOAD_VOICE)
            thumb_f = open(thumb, "rb") if thumb else None
            try:
                with open(mp3, "rb") as f:
                    sent = await ctx.bot.send_audio(
                        chat_id,
                        f,
                        title=title,
                        performer=artist,
                        duration=duration,
                        thumbnail=thumb_f,
                        caption=caption,
                        reply_markup=markup,
                        read_timeout=120,
                        write_timeout=120,
                    )
            finally:
                if thumb_f:
                    thumb_f.close()
            save_meta(vid, title, artist, duration, overwrite=True)
            file_put(vid, quality, sent.audio.file_id)
            add_history(user.id, chat_id, vid)
            await done()
        except Exception as e:  # noqa: BLE001
            log.exception("download failed for %s", vid)
            await done(friendly_error(e))
        finally:
            shutil.rmtree(workdir, ignore_errors=True)


async def handle_query(msg, ctx, user, chat, query: str) -> None:
    ok, reason = await check_access(ctx, chat, user)
    if not ok:
        await deny(msg, reason, chat)
        return
    left = cooldown_left(chat, user)
    if left:
        await msg.reply_text(f"⏳ {left} ثانیه صبر کن.")
        return
    await ctx.bot.send_chat_action(chat.id, ChatAction.TYPING)
    status = await msg.reply_text("🔎 در حال جستجو...")
    try:
        m = URL_RE.search(query)
        if m:
            info = await asyncio.to_thread(_info_sync, m.group(0))
            if not (info.get("extractor_key") or "").lower().startswith("youtube"):
                await status.edit_text("❌ فعلاً فقط لینک یوتیوب پشتیبانی می‌شه.")
                return
            save_meta(
                info["id"],
                info.get("title") or "Unknown",
                info.get("uploader") or "",
                int(info.get("duration") or 0),
            )
            if user.id in ACTIVE:
                await status.edit_text("⏳ درخواست قبلیت هنوز در حال انجامه.")
                return
            ACTIVE.add(user.id)
            try:
                await deliver(ctx, chat, user, info["id"], status, info)
            finally:
                ACTIVE.discard(user.id)
            return
        results = await asyncio.to_thread(_search_sync, query)
    except Exception:  # noqa: BLE001
        log.exception("search failed")
        await status.edit_text("❌ نتونستم پیداش کنم. اسم یا لینک دیگه‌ای امتحان کن.")
        return
    if not results:
        await status.edit_text("❌ چیزی پیدا نشد.")
        return
    sid = new_search(user.id, query, results)
    text, markup = render_search(sid, 0)
    await status.edit_text(text, reply_markup=markup)


async def do_redeem(msg, ctx, user, chat, key: str) -> None:
    key = key.strip().upper()
    if user.id not in OWNER_IDS and is_banned(user.id):
        await msg.reply_text(deny_text("banned", chat))
        return
    if is_group(chat):
        if not await is_admin(ctx, chat.id, user.id):
            await msg.reply_text("🔒 فقط ادمین‌های گروه می‌تونن لایسنس فعال کنن.")
            return
        touch_group(chat)
        subject, kind = chat.id, "group"
        try:  # کد لایسنس تو گروه پاک بشه
            await msg.delete()
        except TelegramError:
            pass
    else:
        subject, kind = user.id, "user"
    status, val = redeem_key(key, subject, kind, user.id)
    if status == "ok":
        who = "گروه" if kind == "group" else "حساب شما"
        text = (
            f"✅ لایسنس فعال شد!\n{who} تا {fdate(val)} ({days_left(val)} روز) اشتراک داره. 🎉"
        )
    elif status == "used":
        text = "❌ این لایسنس قبلاً استفاده شده."
    elif status == "scope":
        text = (
            "❌ این لایسنس فقط برای گروه‌هاست؛ تو گروه با /redeem فعالش کن."
            if val == "group"
            else "❌ این لایسنس فقط برای حساب شخصیه؛ تو چت خصوصی با ربات فعالش کن."
        )
    else:
        text = "❌ لایسنس نامعتبره. دوباره چک کن."
    await ctx.bot.send_message(chat.id, text)


# ============================== هندلرهای دستور ==============================
def register(user) -> bool:
    new = touch_user(user)
    if new and TRIAL_DAYS > 0 and user.id not in OWNER_IDS:
        add_days(user.id, "user", TRIAL_DAYS)
        return True
    return False


async def start_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    trial = register(user)
    if is_group(chat):
        touch_group(chat)
        await msg.reply_text(
            "🎵 من ربات موزیکم!\n\n"
            f"{sub_line(chat.id, group=True)}\n\n"
            "با /play اسم آهنگ، آهنگ می‌گیری. ادمین‌ها با /panel گروه رو مدیریت کنن.",
            reply_markup=Markup([[Btn("⚙️ پنل گروه", callback_data="g:panel")]]),
        )
        return
    ctx.user_data.pop("await_key", None)
    text = home_text(user)
    if trial:
        text = f"🎁 {TRIAL_DAYS} روز اشتراک رایگان برات فعال شد!\n\n" + text
    await msg.reply_text(text, reply_markup=main_menu(user.id))


async def help_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    await update.effective_message.reply_text(HELP_GROUP if is_group(chat) else HELP_PV)


async def profile_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if is_group(chat):
        await msg.reply_text(sub_line(chat.id, group=True))
        return
    touch_user(user)
    text, markup = profile_view(user)
    await msg.reply_text(text, reply_markup=markup)


async def play_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    touch_user(user)
    if is_group(chat):
        touch_group(chat)
    query = " ".join(ctx.args).strip()
    if not query and msg.reply_to_message:
        query = (msg.reply_to_message.text or "").strip()
    if not query:
        await msg.reply_text("استفاده: /play اسم آهنگ یا لینک")
        return
    await handle_query(msg, ctx, user, chat, query)


async def top_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    group = is_group(chat)
    text, markup = list_view("gtop" if group else "top", user.id, chat.id, 0, group)
    await msg.reply_text(text, reply_markup=markup)


async def panel_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    if not is_group(chat):
        await start_cmd(update, ctx)
        return
    touch_group(chat)
    if not await is_admin(ctx, chat.id, user.id):
        await msg.reply_text("🔒 پنل فقط برای ادمین‌های گروهه.")
        return
    text, markup = group_panel(chat)
    await msg.reply_text(text, reply_markup=markup)


async def redeem_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    touch_user(user)
    if not ctx.args:
        await msg.reply_text("استفاده: /redeem کد-لایسنس\nمثلاً: /redeem MB-1A2B-3C4D-5E6F-7A8B")
        return
    await do_redeem(msg, ctx, user, chat, ctx.args[0])


async def cancel_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.pop("await_key", None)
    await update.effective_message.reply_text("لغو شد ✅")


async def private_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    register(user)
    if ctx.user_data.pop("await_key", False):
        await do_redeem(msg, ctx, user, chat, msg.text)
        return
    await handle_query(msg, ctx, user, chat, msg.text.strip())


async def group_reply(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    """جواب به پیام «جستجوی دوباره» ربات تو گروه."""
    msg, user, chat = update.effective_message, update.effective_user, update.effective_chat
    r = msg.reply_to_message
    if not (
        r
        and r.from_user
        and r.from_user.id == ctx.bot.id
        and (r.text or "").startswith(REPLY_PREFIX)
    ):
        return
    touch_user(user)
    touch_group(chat)
    await handle_query(msg, ctx, user, chat, msg.text.strip())


async def on_my_chat_member(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    cm = update.my_chat_member
    chat = cm.chat
    if not is_group(chat):
        return
    if cm.old_chat_member.status in ("left", "kicked") and cm.new_chat_member.status in (
        "member",
        "administrator",
    ):
        touch_group(chat)
        rows = [[Btn("⚙️ پنل گروه", callback_data="g:panel")]]
        b = buy_btn()
        if b:
            rows.append([b])
        try:
            await ctx.bot.send_message(
                chat.id,
                "🎵 سلام! من ربات موزیکم.\n\n"
                "برای استفاده، اشتراک گروه باید فعال باشه: ادمین گروه "
                "/redeem کد-لایسنس رو بزنه.\n"
                "بعدش همه با /play اسم آهنگ آهنگ می‌گیرن.\n"
                "💡 بهتره منو ادمین کنی تا بدون مشکل کار کنم.",
                reply_markup=Markup(rows),
            )
        except TelegramError:
            pass


# ============================== دستورهای مالک ==============================
def owner_only(fn):
    @wraps(fn)
    async def wrapper(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        if not update.effective_user or update.effective_user.id not in OWNER_IDS:
            return
        return await fn(update, ctx)

    return wrapper


@owner_only
async def admin_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text("👑 پنل مالک", reply_markup=admin_markup())


@owner_only
async def genkey_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    a = ctx.args
    if not a or not a[0].isdigit() or int(a[0]) <= 0:
        await update.effective_message.reply_text(
            "استفاده: /genkey 30\n/genkey 30 10 group\n(روز، تعداد، نوع: user / group / any)"
        )
        return
    days, count, scope = int(a[0]), 1, "any"
    for tok in a[1:]:
        if tok in ("user", "group", "any"):
            scope = tok
        elif tok.isdigit():
            count = int(tok)
    count = min(max(count, 1), 50)
    keys = make_keys(days, count, scope, update.effective_user.id)
    text = f"🔑 {count} لایسنس {days} روزه ({scope}):\n\n" + "\n".join(
        f"<code>{k}</code>" for k in keys
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


@owner_only
async def grant_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    a = ctx.args
    try:
        sid, days = int(a[0]), int(a[1])
        assert days > 0
    except (IndexError, ValueError, AssertionError):
        await update.effective_message.reply_text("استفاده: /grant آیدی روز")
        return
    kind = "group" if sid < 0 else "user"
    exp = add_days(sid, kind, days)
    await update.effective_message.reply_text(
        f"✅ اشتراک {sid} تا {fdate(exp)} ({days_left(exp)} روز) فعاله."
    )
    try:
        await ctx.bot.send_message(
            sid, f"🎁 اشتراکت {days} روز تمدید شد! تا {fdate(exp)} فعاله."
        )
    except TelegramError:
        pass


@owner_only
async def revoke_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    try:
        sid = int(ctx.args[0])
    except (IndexError, ValueError):
        await update.effective_message.reply_text("استفاده: /revoke آیدی")
        return
    revoke_sub(sid)
    await update.effective_message.reply_text(f"✅ اشتراک {sid} حذف شد.")


@owner_only
async def ban_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    try:
        uid = int(ctx.args[0])
    except (IndexError, ValueError):
        await update.effective_message.reply_text("استفاده: /ban آیدی")
        return
    db("INSERT OR IGNORE INTO users(user_id, first_seen) VALUES (?,?)", (uid, int(time.time())))
    db("UPDATE users SET banned=1 WHERE user_id=?", (uid,))
    await update.effective_message.reply_text(f"⛔ کاربر {uid} مسدود شد.")


@owner_only
async def unban_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    try:
        uid = int(ctx.args[0])
    except (IndexError, ValueError):
        await update.effective_message.reply_text("استفاده: /unban آیدی")
        return
    db("UPDATE users SET banned=0 WHERE user_id=?", (uid,))
    await update.effective_message.reply_text(f"✅ کاربر {uid} آزاد شد.")


def unused_keys_text() -> str:
    rows = db(
        "SELECT key, days, scope FROM licenses WHERE used_by IS NULL ORDER BY created_at DESC LIMIT 30",
        (),
        "all",
    )
    if not rows:
        return "هیچ لایسنس استفاده‌نشده‌ای نیست."
    return "🔑 لایسنس‌های استفاده‌نشده:\n\n" + "\n".join(
        f"<code>{k}</code> — {d} روز ({s})" for k, d, s in rows
    )


@owner_only
async def keys_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(unused_keys_text(), parse_mode=ParseMode.HTML)


@owner_only
async def stats_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.effective_message.reply_text(global_stats_text())


@owner_only
async def broadcast_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    parts = (update.effective_message.text or "").split(maxsplit=1)
    if len(parts) < 2:
        await update.effective_message.reply_text("استفاده: /broadcast متن پیام")
        return
    text = parts[1]
    targets = [r[0] for r in db("SELECT user_id FROM users WHERE banned=0", (), "all")]
    targets += [r[0] for r in db("SELECT chat_id FROM groups", (), "all")]
    sent = 0
    for t in targets:
        try:
            await ctx.bot.send_message(t, text)
            sent += 1
        except TelegramError:
            pass
        await asyncio.sleep(0.05)
    await update.effective_message.reply_text(f"📣 برای {sent} از {len(targets)} نفر/گروه ارسال شد.")


# ============================== دکمه‌ها (callback) ==============================
async def cb_noop(q, ctx, p):
    await q.answer()


async def cb_download(q, ctx, p):
    vid, owner = p[0], int(p[1])
    user, msg = q.from_user, q.message
    chat = msg.chat
    if owner and user.id != owner:
        await q.answer("این لیست برای کس دیگه‌ست؛ خودت /play بزن 😉", show_alert=True)
        return
    ok, reason = await check_access(ctx, chat, user)
    if not ok:
        await q.answer(deny_text(reason, chat), show_alert=True)
        return
    if user.id in ACTIVE:
        await q.answer("⏳ درخواست قبلیت هنوز در حال انجامه.", show_alert=True)
        return
    ACTIVE.add(user.id)
    try:
        await q.answer("⏳ در حال آماده‌سازی...")
        status = await ctx.bot.send_message(chat.id, "⬇️ در حال دانلود و آپلود...")
        if (
            is_group(chat)
            and get_group(chat.id)["clean"]
            and (getattr(msg, "text", None) or "").startswith(("🔎", "🎼"))
        ):
            try:
                await msg.delete()
            except TelegramError:
                pass
        await deliver(ctx, chat, user, vid, status)
    finally:
        ACTIVE.discard(user.id)


async def cb_page(q, ctx, p):
    sid, page = p[0], int(p[1])
    s = SEARCHES.get(sid)
    if not s:
        await q.answer("نتایج منقضی شده؛ دوباره جستجو کن.", show_alert=True)
        return
    if s["uid"] != q.from_user.id:
        await q.answer("این نتایج برای کس دیگه‌ست.", show_alert=True)
        return
    await q.answer()
    text, markup = render_search(sid, page)
    await show(q, ctx, text, markup)


async def cb_fav(q, ctx, p):
    added = fav_toggle(q.from_user.id, p[0])
    await q.answer(
        "❤️ به علاقه‌مندی‌ها اضافه شد" if added else "💔 از علاقه‌مندی‌ها حذف شد"
    )


async def cb_similar(q, ctx, p):
    vid = p[0]
    user, msg = q.from_user, q.message
    chat = msg.chat
    ok, reason = await check_access(ctx, chat, user)
    if not ok:
        await q.answer(deny_text(reason, chat), show_alert=True)
        return
    left = cooldown_left(chat, user)
    if left:
        await q.answer(f"⏳ {left} ثانیه صبر کن.", show_alert=True)
        return
    await q.answer("🎼 در حال پیدا کردن آهنگ‌های مشابه...")
    meta = get_meta(vid) or {}
    results = await asyncio.to_thread(
        _similar_sync, vid, meta.get("title", ""), meta.get("artist", "")
    )
    if not results:
        await msg.reply_text("❌ آهنگ مشابهی پیدا نشد.")
        return
    sid = new_search(user.id, meta.get("title") or "این آهنگ", results, "similar")
    text, markup = render_search(sid, 0)
    await msg.reply_text(text, reply_markup=markup)


async def cb_again(q, ctx, p):
    user, chat = q.from_user, q.message.chat
    ok, reason = await check_access(ctx, chat, user)
    if not ok:
        await q.answer(deny_text(reason, chat), show_alert=True)
        return
    await q.answer()
    if is_group(chat):
        await ctx.bot.send_message(
            chat.id,
            f"{REPLY_PREFIX} رو ریپلای کن ({user.mention_html()})",
            parse_mode=ParseMode.HTML,
            reply_markup=ForceReply(selective=True, input_field_placeholder="اسم آهنگ یا لینک"),
        )
    else:
        await ctx.bot.send_message(chat.id, "🔎 اسم آهنگ یا لینک یوتیوب رو بفرست:")


async def cb_close(q, ctx, p):
    owner = int(p[0]) if p else 0
    user, msg = q.from_user, q.message
    chat = msg.chat
    allowed = (
        not is_group(chat)
        or (owner and user.id == owner)
        or await is_admin(ctx, chat.id, user.id)
    )
    if not allowed:
        await q.answer("🔒 فقط خودش یا ادمین‌ها.", show_alert=True)
        return
    await q.answer()
    try:
        await msg.delete()
    except TelegramError:
        pass


async def cb_list(q, ctx, p):
    kind, page = p[0], int(p[1])
    chat = q.message.chat
    group = is_group(chat)
    if kind == "gtop" and not group:
        kind = "top"
    await q.answer()
    text, markup = list_view(kind, q.from_user.id, chat.id, page, group)
    await show(q, ctx, text, markup)


async def cb_menu(q, ctx, p):
    user, chat = q.from_user, q.message.chat
    if is_group(chat):
        await q.answer()
        return
    sub = p[0]
    await q.answer()
    if sub == "home":
        ctx.user_data.pop("await_key", None)
        await show(q, ctx, home_text(user), main_menu(user.id))
    elif sub == "search":
        await ctx.bot.send_message(chat.id, "🔎 اسم آهنگ یا لینک یوتیوب رو بفرست:")
    elif sub == "sub":
        text, markup = profile_view(user)
        await show(q, ctx, text, markup)
    elif sub == "set":
        text, markup = settings_view(user.id)
        await show(q, ctx, text, markup)
    elif sub == "help":
        await show(
            q, ctx, HELP_PV, Markup([[Btn("🏠 منو", callback_data="m:home")]])
        )
    elif sub == "key":
        ctx.user_data["await_key"] = True
        await ctx.bot.send_message(
            chat.id, "🔑 کد لایسنس رو بفرست (مثل MB-1A2B-3C4D-5E6F-7A8B).\nبرای لغو: /cancel"
        )


async def cb_settings(q, ctx, p):
    if len(p) == 2 and p[0] == "q" and p[1] in ("128", "192", "320"):
        touch_user(q.from_user)
        db("UPDATE users SET quality=? WHERE user_id=?", (int(p[1]), q.from_user.id))
        await q.answer("✅ ذخیره شد")
        text, markup = settings_view(q.from_user.id)
        await show(q, ctx, text, markup)
    else:
        await q.answer()


async def cb_group(q, ctx, p):
    chat, user = q.message.chat, q.from_user
    if not is_group(chat):
        await q.answer()
        return
    if not await is_admin(ctx, chat.id, user.id):
        await q.answer("🔒 فقط ادمین‌های گروه.", show_alert=True)
        return
    touch_group(chat)
    act = p[0]
    cfg = get_group(chat.id)
    if act == "mode":
        set_group(chat.id, "mode", "admins" if cfg["mode"] == "all" else "all")
    elif act == "cd":
        seq = [0, 3, 5, 10, 30, 60]
        nxt = seq[(seq.index(cfg["cooldown"]) + 1) % len(seq)] if cfg["cooldown"] in seq else 5
        set_group(chat.id, "cooldown", nxt)
    elif act in ("btn", "clean"):
        field = "buttons" if act == "btn" else "clean"
        set_group(chat.id, field, 0 if cfg[field] else 1)
    elif act == "key":
        await q.answer()
        await ctx.bot.send_message(
            chat.id,
            "🔑 برای فعال‌سازی یا تمدید اشتراک گروه، یکی از ادمین‌ها بنویسه:\n"
            "/redeem کد-لایسنس\n(پیام کد بعد از فعال‌سازی خودکار پاک می‌شه)",
        )
        return
    elif act == "stats":
        await q.answer()
        await show(
            q,
            ctx,
            group_stats_text(chat.id),
            Markup([[Btn("🔙 پنل", callback_data="g:panel")]]),
        )
        return
    elif act == "panel":
        await q.answer()
        text, markup = group_panel(chat)
        await show(q, ctx, text, markup)
        return
    else:
        await q.answer()
        return
    await q.answer("✅ ذخیره شد")
    text, markup = group_panel(chat)
    await show(q, ctx, text, markup)


async def cb_admin(q, ctx, p):
    if q.from_user.id not in OWNER_IDS:
        await q.answer("🔒", show_alert=True)
        return
    await q.answer()
    back = Markup([[Btn("🔙 پنل", callback_data="a:home")]])
    if p[0] == "stats":
        await show(q, ctx, global_stats_text(), back)
    elif p[0] == "keys":
        await show(q, ctx, unused_keys_text(), back, ParseMode.HTML)
    elif p[0] == "help":
        await show(q, ctx, ADMIN_HELP, back)
    else:
        await show(q, ctx, "👑 پنل مالک", admin_markup())


CB = {
    "noop": cb_noop,
    "dl": cb_download,
    "pg": cb_page,
    "f": cb_fav,
    "s": cb_similar,
    "r": cb_again,
    "x": cb_close,
    "ls": cb_list,
    "m": cb_menu,
    "st": cb_settings,
    "g": cb_group,
    "a": cb_admin,
}


async def on_callback(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    user = q.from_user
    touch_user(user)
    if user.id not in OWNER_IDS and is_banned(user.id):
        await q.answer("⛔ دسترسی شما مسدوده.", show_alert=True)
        return
    cmd, *p = (q.data or "").split(":")
    handler = CB.get(cmd)
    try:
        if handler is None:
            await q.answer()
        else:
            await handler(q, ctx, p)
    except Exception:  # noqa: BLE001
        log.exception("callback error: %s", q.data)
        try:
            await q.answer("❌ خطای غیرمنتظره. دوباره امتحان کن.", show_alert=True)
        except TelegramError:
            pass


# ============================== کارهای زمان‌بندی‌شده ==============================
async def expiry_job(ctx: ContextTypes.DEFAULT_TYPE):
    now = int(time.time())
    rows = db(
        "SELECT subject_id FROM subs WHERE notified=0 AND expires_at BETWEEN ? AND ?",
        (now, now + 86400),
        "all",
    )
    for (sid,) in rows:
        mk = None
        b = buy_btn()
        if b:
            mk = Markup([[b]])
        try:
            await ctx.bot.send_message(
                sid,
                "⏰ اشتراکت کمتر از ۱ روز دیگه تموم می‌شه.\nبرای تمدید با /redeem لایسنس جدید فعال کن.",
                reply_markup=mk,
            )
        except TelegramError:
            pass
        db("UPDATE subs SET notified=1 WHERE subject_id=?", (sid,))
    rows = db(
        "SELECT subject_id FROM subs WHERE notified<2 AND expires_at<?", (now,), "all"
    )
    for (sid,) in rows:
        b = buy_btn()
        mk = Markup([[b]]) if b else None
        try:
            await ctx.bot.send_message(
                sid,
                "⛔ اشتراکت تموم شد. برای ادامه، لایسنس جدید رو با /redeem فعال کن.",
                reply_markup=mk,
            )
        except TelegramError:
            pass
        db("UPDATE subs SET notified=2 WHERE subject_id=?", (sid,))


async def post_init(app: Application):
    try:
        await app.bot.set_my_commands(
            [
                BotCommand("start", "منوی اصلی"),
                BotCommand("play", "جستجوی آهنگ"),
                BotCommand("top", "پرطرفدارها"),
                BotCommand("profile", "پروفایل و اشتراک"),
                BotCommand("redeem", "فعال‌سازی لایسنس"),
                BotCommand("help", "راهنما"),
            ],
            scope=BotCommandScopeAllPrivateChats(),
        )
        await app.bot.set_my_commands(
            [
                BotCommand("play", "جستجوی آهنگ"),
                BotCommand("top", "پرطرفدارهای گروه"),
                BotCommand("panel", "پنل مدیریت گروه"),
                BotCommand("redeem", "فعال‌سازی لایسنس گروه"),
                BotCommand("help", "راهنما"),
            ],
            scope=BotCommandScopeAllGroupChats(),
        )
    except TelegramError:
        log.warning("set_my_commands failed", exc_info=True)


async def on_error(update, ctx: ContextTypes.DEFAULT_TYPE):
    log.error("Unhandled error", exc_info=ctx.error)


def build_app() -> Application:
    db_init()
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .concurrent_updates(True)
        .post_init(post_init)
        .build()
    )
    add = app.add_handler
    add(CommandHandler("start", start_cmd))
    add(CommandHandler(["help", "menu"], help_cmd))
    add(CommandHandler(["play", "p", "music"], play_cmd))
    add(CommandHandler("top", top_cmd))
    add(CommandHandler("panel", panel_cmd))
    add(CommandHandler("profile", profile_cmd))
    add(CommandHandler("redeem", redeem_cmd))
    add(CommandHandler("cancel", cancel_cmd))
    add(CommandHandler("admin", admin_cmd))
    add(CommandHandler("genkey", genkey_cmd))
    add(CommandHandler("grant", grant_cmd))
    add(CommandHandler("revoke", revoke_cmd))
    add(CommandHandler("ban", ban_cmd))
    add(CommandHandler("unban", unban_cmd))
    add(CommandHandler("keys", keys_cmd))
    add(CommandHandler("stats", stats_cmd))
    add(CommandHandler("broadcast", broadcast_cmd))
    add(CallbackQueryHandler(on_callback))
    add(ChatMemberHandler(on_my_chat_member, ChatMemberHandler.MY_CHAT_MEMBER))
    add(
        MessageHandler(
            filters.ChatType.PRIVATE & filters.TEXT & ~filters.COMMAND, private_text
        )
    )
    add(
        MessageHandler(
            filters.ChatType.GROUPS & filters.REPLY & filters.TEXT & ~filters.COMMAND,
            group_reply,
        )
    )
    app.add_error_handler(on_error)
    if app.job_queue:
        app.job_queue.run_repeating(expiry_job, interval=3600, first=60)
    else:
        log.warning("job-queue نصب نیست؛ یادآوری تمدید کار نمی‌کنه.")
    return app


def main():
    if not OWNER_IDS:
        log.warning("OWNER_IDS خالیه؛ هیچ‌کس نمی‌تونه لایسنس بسازه!")
    if not shutil.which("ffmpeg"):
        log.warning("ffmpeg پیدا نشد! بدون اون آهنگ‌ها دانلود نمی‌شن. (بعد از نصب، PowerShell رو ببند و دوباره باز کن)")
    app = build_app()
    log.info("Bot started")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
