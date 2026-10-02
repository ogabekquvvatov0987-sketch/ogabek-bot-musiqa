# Kerakli kutubxonalarni import qilish
import asyncio
import os
import time
import re
import sqlite3
import hashlib
import urllib.parse
import urllib.request
import json
from html.parser import HTMLParser
import glob
import yt_dlp
from yt_dlp.utils import DownloadError
from datetime import datetime, timedelta, timezone
import logging
import random
import openpyxl
from functools import partial
import speech_recognition as sr # type: ignore[import]
from pydub import AudioSegment
import edge_tts
try:
    from shazamio import Shazam  # type: ignore[import]
    SHAZAM_AVAILABLE = True
except ImportError:
    Shazam = None  # type: ignore[assignment]
    SHAZAM_AVAILABLE = False
try:
    from deep_translator import GoogleTranslator  # type: ignore[import]
    GOOGLE_TRANSLATOR_AVAILABLE = True
except ImportError:
    GoogleTranslator = None  # type: ignore[assignment]
    GOOGLE_TRANSLATOR_AVAILABLE = False
from html import escape
# Rasmga ishlov berish uchun
from PIL import Image, ImageOps
try:
    from rembg import remove as remove_bg  # type: ignore[import]
    REMBG_AVAILABLE = True
except ImportError:
    remove_bg = None  # type: ignore[assignment]
    REMBG_AVAILABLE = False
try:
    from pyrogram import Client  # type: ignore[import]
    from pyrogram.errors import SessionRevoked, AuthKeyUnregistered, UserDeactivated  # type: ignore[import]
    PYROGRAM_AVAILABLE = True
except ImportError:
    Client = None  # type: ignore[assignment]
    SessionRevoked = AuthKeyUnregistered = UserDeactivated = Exception
    PYROGRAM_AVAILABLE = False
from typing import Any, Awaitable, Callable, Dict, Union, List, Tuple, Optional, Set
from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, Router, F
from aiogram.filters import CommandStart, Command, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.exceptions import TelegramForbiddenError, TelegramBadRequest
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    Message,
    CallbackQuery,
    ReplyKeyboardRemove,
    ContentType,
    KeyboardButton,
    InlineKeyboardButton)
from aiogram.types import FSInputFile
from aiogram.utils.keyboard import ReplyKeyboardBuilder, InlineKeyboardBuilder
from database import Database

# ============================================================
# Konfigurasiya va logging
# ============================================================
load_dotenv()

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", handlers=[logging.StreamHandler()])
logging.getLogger("pyrogram").setLevel(logging.WARNING)
logging.getLogger("yt_dlp").setLevel(logging.WARNING)
logging.getLogger("aiohttp").setLevel(logging.WARNING)
logger = logging.getLogger(__name__)

# Papka yo'lini aniqlash
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

def _harden_local_secrets():
    """Cookie/session/.env fayllarini serverda boshqa local userlardan yopadi."""
    for name in (".env", "my_account.session", "my_account.session-journal", "youtube_cookies.txt", "instagram_cookies.txt", "cookies.txt"):
        path = os.path.join(BASE_DIR, name)
        try:
            if os.path.isfile(path):
                os.chmod(path, 0o600)
        except OSError:
            pass

_harden_local_secrets()

BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")

ADMIN_IDS: List[int] = [
    int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()
]
CHANNEL_LINKS: list[str] = (
    os.getenv("CHANNEL_LINKS", "").split(",")
    if os.getenv("CHANNEL_LINKS")
    else []
)
UPLOAD_CHANNEL_ID = os.getenv("UPLOAD_CHANNEL_ID") # Katta videolarni yuklash uchun kanal IDsi

# Pyrogram (Userbot) sozlamalari - Katta fayllar (50MB+) uchun
API_ID = os.getenv("API_ID")
API_HASH = os.getenv("API_HASH")
user_bot: Any = None
# Userbot session faylini tozalash (agar SESSION_REVOKED xatosi bo'lsa)
userbot_session_path = os.path.join(BASE_DIR, "my_account.session")
userbot_session_journal_path = os.path.join(BASE_DIR, "my_account.session-journal")
# Session faylini avtomatik o'chirmaymiz - faqat xato bo'lsa o'chiramiz
USERBOT_SESSION_NEEDS_RESET = False
USERBOT_START_MAX_RETRIES = 3
USERBOT_START_BACKOFF_SECONDS = 2

# Cookie fayllar yo'li - Kali Linux uchun moslashtirilgan
INSTAGRAM_COOKIES_PATH = os.path.join(BASE_DIR, "instagram_cookies.txt") # Instagram cookie fayli
# YouTube uchun cookie fayllar ro'yxati (Kali Linux uchun moslashtirilgan)
YOUTUBE_COOKIE_FILES = [
    os.path.join(BASE_DIR, "youtube_cookies.txt"),
    os.path.join(BASE_DIR, "www.youtube.com_cookies.txt"),
    os.path.join(BASE_DIR, "cookies.txt"),
    os.path.join(BASE_DIR, "cookies (1).txt"),
]
YOUTUBE_BROWSER_PROFILES = ("chromium", "brave", "chrome", "firefox")

def _browser_available(browser_name: str) -> bool:
    """yt-dlp cookies-from-browser uchun brauzer haqiqatan o'rnatilganini tekshiradi."""
    import shutil
    candidates = {
        "brave": ("brave-browser", "brave-browser-stable", "brave"),
        "chromium": ("chromium", "chromium-browser"),
        "chrome": ("google-chrome", "google-chrome-stable", "chrome"),
        "firefox": ("firefox",),
    }
    return any(shutil.which(x) for x in candidates.get(browser_name, ()))


def youtube_auth_sources():
    """YouTube auth: ishlaydigan cookie fayllari -> login qilingan browser -> cookiesiz."""
    sources = []
    for path in YOUTUBE_COOKIE_FILES:
        if os.path.isfile(path) and os.path.getsize(path) > 100:
            sources.append(("file", path))

    # Avval foydalanuvchi eng ko'p ishlatadigan Brave/Chromium'ni sinaymiz.
    for browser in ("brave", "chromium", "chrome", "firefox"):
        if _browser_available(browser):
            sources.append(("browser", browser))

    # Faqat oxirgi fallback. Bu urinishning o'zi auth muammosini yashirmasligi uchun
    # logda aniq "cookiesiz" deb ko'rsatiladi.
    sources.append(("none", None))
    return sources


def instagram_auth_sources():
    """Instagram auth: cookie fayli -> mavjud browserlar -> cookiesiz."""
    sources = []
    if os.path.isfile(INSTAGRAM_COOKIES_PATH) and os.path.getsize(INSTAGRAM_COOKIES_PATH) > 100:
        sources.append(("file", INSTAGRAM_COOKIES_PATH))
    for browser in ("brave", "chromium", "chrome", "firefox"):
        if _browser_available(browser):
            sources.append(("browser", browser))
    sources.append(("none", None))
    return sources


def apply_browser_auth(ydl_options: dict, auth_source):
    source_type, source_value = auth_source
    # Bir urinishda oldingi cookie sozlamasi qolib ketmasligi kerak.
    ydl_options.pop("cookiefile", None)
    ydl_options.pop("cookiesfrombrowser", None)
    if source_type == "file":
        ydl_options["cookiefile"] = source_value
    elif source_type == "browser":
        ydl_options["cookiesfrombrowser"] = (source_value,)


def apply_youtube_auth(ydl_options, auth_source):
    apply_browser_auth(ydl_options, auth_source)


# 2026: SABR/PO-Token muammolariga chidamli clientlar.
# YouTube uchun barqaror clientlar.
# "tv_downgraded" va ayrim cookie/client kombinatsiyalari 2026-yilda
# "The page needs to be reloaded" xatosini keltirishi mumkin.
YOUTUBE_PLAYER_CLIENTS = ["default"]


def get_youtube_ydl_opts(fmt: str, outtmpl: str, progress_hook=None, extra: dict = None) -> dict:
    """YouTube yuklash uchun umumiy, mustahkam yt-dlp sozlamalari."""
    opts = {
        "format": fmt,
        "outtmpl": outtmpl,
        "noplaylist": True,
        "quiet": True,
        "no_warnings": True,
        "ignoreerrors": False,
        "nocheckcertificate": False,
        "geo_bypass": True,
        "socket_timeout": 45,
        "retries": 8,
        "fragment_retries": 8,
        "file_access_retries": 3,
        "retry_sleep_functions": {"http": lambda n: min(2 ** n, 10)},
        "merge_output_format": "mp4",
        "http_headers": {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/131.0.0.0 Safari/537.36"
            ),
            "Accept-Language": "en-US,en;q=0.9",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        },
        "extractor_args": {
            "youtube": {
                "player_client": YOUTUBE_PLAYER_CLIENTS,
            }
        },
    }
    if progress_hook:
        opts["progress_hooks"] = [progress_hook]
    if extra:
        if "extractor_args" in extra:
            base_ea = opts.setdefault("extractor_args", {})
            for k, v in extra["extractor_args"].items():
                if k in base_ea and isinstance(base_ea[k], dict) and isinstance(v, dict):
                    base_ea[k].update(v)
                else:
                    base_ea[k] = v
            extra = {**extra}
            del extra["extractor_args"]
            opts["extractor_args"] = base_ea
        # None qiymatlarni olib tashlash
        extra = {k: v for k, v in extra.items() if v is not None}
        opts.update(extra)
    return opts

# ============================================================
# Global ob'ektlar
# ============================================================
storage = MemoryStorage()
router = Router()
# Server yuklamasini boshqarish
MAX_CONCURRENT_DOWNLOADS = 3  # Resurslarni himoya qilish va tezkor javob uchun
download_semaphore = asyncio.Semaphore(MAX_CONCURRENT_DOWNLOADS)
db = Database() # Database instance
DOWNLOADING_USERS = set() # In-memory set for current downloads

# /start buyrug'i uchun Rate limiting
START_COMMAND_LIMITS = {}  # {user_id: [timestamp1, ...]}
TEMP_BLOCKS: Dict[int, float] = {}
UZ_TIMEZONE = timezone(timedelta(hours=5))

# Regex patterns
YOUTUBE_PATTERN = re.compile(r'(?:youtube\.com\/(?:[^\/]+\/.+\/|(?:v|e(?:mbed)?|shorts)\/|.*[?&]v=)|youtu\.be\/)([^"&?\/\s]{11})')
INSTAGRAM_PATTERN = re.compile(r'instagram\.com/(p|reel|tv|stories)/([^/?#&]+)')
FACEBOOK_PATTERN = re.compile(r'(?:facebook\.com|fb\.watch|fb\.com|facebook\.com/share)')

# ============================================================
# FSM Holatlar
# ============================================================
class UserStates(StatesGroup):
    captcha = State()
    full_name = State()
    region = State()
    district = State()
    neighborhood = State()
    phone = State()
    location = State()
    edit_full_name = State()
    edit_region = State()
    edit_district = State()
    edit_neighborhood = State()
    edit_phone = State()
    edit_location = State()
    confirm_delete = State()
    feedback = State()
    like_feedback = State()
    rating_feedback = State()
    comment_feedback = State()
    support_chat = State()
    music_search = State()
    my_music = State()
    settings = State()
    video_to_mp3 = State()
    voice_to_text = State()
    text_to_voice = State()
    shazam_mode = State()
    tts_voice_select = State()
    edit_music = State()
    # Reklama xizmatlari uchun yangi holatlar
    my_music_search = State()
    ads_menu = State()
    ads_platform = State()
    ads_text = State()
    ads_ask_media = State()
    ads_media = State()
    ads_confirm = State()
    ads_edit_select = State()
    ads_edit_input = State()
    video_download = State()
    my_videos = State()
    # Rasm bo'limi holatlari
    image_menu = State()
    image_rm_bg = State()
    image_filter = State()
    complaint = State() # Bloklangan foydalanuvchi shikoyati uchun yangi holat
    order = State()
    round_video = State()
    edit_video_caption = State()
    my_images = State()
    edit_image_caption = State()

class TranslationStates(StatesGroup):
    select_source_lang = State()
    enter_text = State()
    select_target_lang = State()

class AdminStates(StatesGroup):
    broadcast = State()
    user_selection = State()
    search_user_id = State()
    banned_selection = State()
    send_notification = State()
    confirm_unblock = State() # Blokdan chiqarishni tasdiqlash
    viewing_orders = State()
    add_channel = State()
    upload_video_guide = State()


# ============================================================
# Statik ma'lumotlar
# ============================================================
REGIONS = [
    "Toshkent", "Andijon", "Buxoro", "Qashqadaryo", "Namangan",
    "Navoiy", "Jizzax", "Surxondaryo", "Sirdaryo", "Farg'ona",
    "Xorazm", "Qoraqalpog'iston",
]

DISTRICTS = {
    "Surxondaryo": [
        "Sherobod", "Bandixon", "Qumqo'rgʻon", "Muzrabot",
        "Qiziriq", "Jarqo'rg'on", "Boysun", "Sariosiyo", "Uzun", "Angor",
        "Termiz shahri", "Termiz tumani", "Oltinsoy", "Denov", "Sho'rchi"
    ],
}

NEIGHBORHOODS = {
    "Sherobod": [
        "Oyinli", "Xo'jaqiya-1", "Xo'jaqiya-2", "G'urjak-1", "G'urjak-2",
        "Bog'iobod", "Nurtepa", "Qizil olma", "Zarabog'", "Qorabog'",
        "Galaguzar", "Boybuloq", "Taroqli", "Majnuntol", "Mehrobod",
        "Vandob", "G'ambur", "Qo'rg'on", "Bahor", "Buyuk ipak yo'li",
        "Yoshlik", "Boyqishloq", "Do'stlik", "Dehqonariq", "Gulchinor", 
        "G'o'rin Gilambob", "Guliston", "Mehnatabod", "Oqtepa", "Qulluqsho", 
        "Qishloqbozor", "Katta hayot", "Katta bog'", "Istiqbol", "Uzunsoy", 
        "Uch yog'och", "Oltin voha", "Hakimobod", "Navbur", "Sherobod", 
        "Cho'yinchi", "Chuqurko'l", "Xo'jgi", "Cho'mishli", "Balxiguzar",
        "Chag'atoy", "Poshxurt",
    ]
}

# Tarjimalar
TRANSLATIONS = {
    "uz": {
        "translate": "🔄 Tarjima",
        "select_source_language": "Qaysi tildan tarjima qilmoqchisiz?",
        "welcome_main": "Bosh menyuga xush kelibsiz! 🌟",
        "ads": "📢 Reklama olami",
        "new_ad_order_admin": "🆕 Yangi reklama buyurtmasi: {order_id}\nIltimos, admin panelni tekshiring.",
        "music": "🎵 Musiqa olami",
        "support": "🆘 Qo'llab-quvvatlash",
        "profile_status_header": "\n\n—\n📊 <b>Profil holati:</b>\n",
        "image_section": "🖼 Rasm olami",
        "btn_remove_bg": "✂️ Fonni olib tashlash",        
        "profile_daily_stats": "\n\n—\n📊 <b>Bugungi statistika:</b>\n📥 Jami yuklashlar: {count} ta",
        "btn_filter": "🎨 Rangni o'zgartirish (B&W)",
        "rembg_not_installed": "⚠️ 'rembg' kutubxonasi serverda o'rnatilmagan.",
        "send_photo_bg": "Rasmni yuboring, men uning fonini olib tashlayman 📤",
        "send_photo_filter": "Rasmni yuboring, men uni oq-qora formatga oʻtkazaman 📤",
        "save_image": "💾 Saqlash",
        "processing_image": "🖼 Rasm qayta ishlanmoqda... Iltimos kuting ⏳",
        "back_to_images": "⬅️ Rasmlar bo'limiga",
        "feedback": "💬 Fikr va takliflar",
        "profile_header_admin": "<b>📋 Foydalanuvchi profil ma'lumotlari:</b>",
        "profile_status_excellent": "✅ {name}, sizning profilingiz to'liq va a'lo darajada! Sizga 5 ball!",
        "profile_status_good": "👍 {name}, profilingiz deyarli to'liq. Sizga 4 ball.",
        "welcome_main": "Bosh menyuga xush kelibsiz! 🌟",
        "profile_status_satisfactory": "😐 {name}, profilingiz qoniqarli. Sizga 3 ball. Tuman yoki mahalla kabi ma'lumotlarni to'ldirishni tavsiya qilamiz.",
        "profile_status_poor": "😕 {name}, profilingizda ma'lumotlar kam. Sizga 2 ball. Iltimos, profilingizni to'ldiring.",
        "profile_status_very_poor": "👎 {name}, profilingiz bo'sh. Sizga 1 ball. Iltimos, 'Tahrirlash' tugmasi orqali ma'lumotlarni kiriting.",
        "profile": "👤 Profil",
        "about": "🤖 Bot haqida",
        "admin": "🔰 Admin panel",
        "settings": "⚙️ Sozlamalar",
        "share_location": "📍 Joylashuvni ulashish",
        "back_main": "🏠 Bosh menyuga",
        "select_lang": "Tilni tanlang:",
        "save": "💾 Saqlash",
        "saved": "Saqlandi! ✅",
        "cancel": "❌ Bekor qilish",
        "selected": "Tanlandi: {l_name}",
        "lang_uz": "🇺🇿 O'zbekcha",
        "lang_ru": "🇷🇺 Русский",
        "lang_en": "🇬🇧 English",
        "select_target_language": "Qaysi tilga tarjima qilmoqchisiz?",
        "enter_text_for_translation": "Tarjima uchun matn kiriting:",
        "searching_music": "🔍 Musiqa qidirilmoqda... Biroz kuting.",
        "press_to_download": "⬇️ <i>Yuklab olish uchun raqamni tanlang:</i>",
        "btn_prev_page": "⬅️ Orqaga",
        "btn_next_page": "Oldinga ➡️",
        "music_download_wait": "📥 Musiqa yuklanmoqda... Biroz kuting, sabr-toqatingiz uchun rahmat.",
        "all_data_restored": "Barcha ma'lumotlaringiz muvaffaqiyatli tiklandi! ✅",
        "admin_data": "📂 Ma'lumotlar",
        "temp_blocked": "🚫 {name}, siz vaqtincha bloklangansiz!\n⏳ {wait_time} daqiqa kuting.",
        "delete_all": "🗑 Barchasini o'chirish",
        "confirm_delete_all_videos": "⚠️ <b>Diqqat!</b>\n\nRostdan ham barcha saqlangan videolarni o'chirmoqchimisiz?",
        "deleted_all_videos_restore": "🗑 <b>Siz barcha videolarni o'chirgansiz.</b>\n\nUlarni qayta tiklashni xohlaysizmi?",
        "btn_restore": "♻️ Tiklash",
        "all_restored": "Barchasi tiklandi! ✅",
        "admin_stats_menu": "📊 Statistika menyusi. Ko'rish uchun davrni tanlang:",
        "stats_daily": "📅 Kunlik",
        "stats_weekly": "📅 Haftalik",
        "stats_monthly": "📅 Oylik",
        # Reklama bo'limi tarjimalari
        "ads_choose_type": "Qanday turdagi reklama xizmatidan foydalanmoqchisiz? 👇",
        "video_guide_btn": "📹 Video qo'llanma",
        "admin_video_guide_menu": "Video qo'llanmani boshqarish:",
        "upload_guide_btn": "📤 Yuklash / Tahrirlash",
        "delete_guide_btn": "🗑 O'chirish",
        "send_video_guide_prompt": "Iltimos, video qo'llanmani yuboring.",
        "guide_uploaded_success": "✅ Video qo'llanma muvaffaqiyatli yuklandi!",
        "guide_deleted_success": "🗑 Video qo'llanma o'chirildi.",
        "no_guide_available": "Hozircha video qo'llanma mavjud emas.",
        "confirm_delete_guide": "Haqiqatdan ham video qo'llanmani o'chirmoqchimisiz?",
        "admin_broadcast_prompt": "Elon uchun xabarni yuboring (matn, rasm, video, va hokazo): 📢",
        "refresh_btn": "🔄 Yangilash",
        "admin_granted": "✅ Foydalanuvchi admin qilindi!",
        "admin_revoked": "❌ Foydalanuvchi adminlikdan olindi!",
        "special_granted": "✅ Foydalanuvchiga barcha cheklovlar olib tashlandi!",
        "special_revoked": "❌ Foydalanuvchi uchun cheklovlar tiklandi!",
        "ads_social": "📱 Ijtimoiy tarmoq reklamasi",
        "ads_simple_text": "📝 Oddiy matn reklamasi",
        "ads_choose_platform": "Iltimos, qaysi ijtimoiy tarmoqda reklama bermoqchisiz? 👇",
        "ads_platform_insta": "📸 Instagram",
        "ads_platform_tg": "✈️ Telegram",
        "ads_platform_all": "🌐 Barcha tarmoqda",
        "ads_enter_text": "Iltimos, reklama matnini kiriting va kerakli ma'lumotlarni berib o'ting: 📝",
        "ads_ask_media": "Biriktiradigan <b>fayl yoki mediangiz</b> bormi? 📎",
        "ads_send_media": "Iltimos, <b>media faylni</b> (Rasm yoki Video) yuboring: 📤",
        "ads_confirm_title": "📋 <b>Buyurtmani tasdiqlash:</b>\nIltimos, ma'lumotlarni tekshiring:",
        "ads_btn_confirm": "✅ Tasdiqlash",
        "ads_btn_edit": "✏️ <b>Tahrirlash</b>",
        "ads_btn_cancel": "❌ Bekor qilish",
        "ads_order_sent": "✅ {name}, buyurtmangiz qabul qilindi! Tez orada adminlarimiz siz bilan bog'lanishadi.",
        "ads_edit_what": "Qaysi qismni tahrirlamoqchisiz?",
        "ads_edit_platform": "📱 Tarmoqni o'zgartirish",
        "ads_edit_media": "📷 Mediani o'zgartirish",
        "ads_edit_text": "📝 Matnni o'zgartirish",
        "ads_save_changes": "Yangi ma'lumotlarni saqlaysizmi? 💾",
        "ads_saved": "O'zgarishlar saqlandi! ✅",
        "order_status_completed_msg": "Hurmatli foydalanuvchi! Sizning buyurtmangiz ko'rib chiqildi. Mutaxassislarimiz siz bilan bog'lanishini kuting. ✅",
        "order_status_later_msg": "Hurmatli foydalanuvchi! Buyurtmangiz ko'rib chiqish bosqichida. Kuting, bizni tanlaganingiz uchun rahmat! ⏳",
        "btn_completed": "✅ Bajarildi",
        "btn_later": "⏳ Keyinroq",
        "ads_type_social": "Ijtimoiy tarmoq",
        "ads_type_simple": "Oddiy matn",
        "yes": "✅ Ha",
        "no": "❌ Yo'q",
        "voice_to_text_btn": "🗣 Ovoz va Matn",
        "video_to_mp3_btn": "📹 Videoni MP3 ga aylantirish",
        "voice_to_text_prompt": "🗣 <b>Ovoz va Matn konverteri</b>\n\nKerakli xizmatni tanlang: 👇",
        "video_to_mp3_prompt": "📹 <b>Videoni MP3 ga aylantirish</b>\n\nIstalgan videoni yuboring, men uni audio (MP3) formatga o'girib beraman. 🎵",
        "video_section": "📹 Video olami",
        "round_video_btn": "⭕️ Dumaloq video",
        "video_link_btn": "🔗 Video havolasi",
        "video_link_prompt_extended": "🔗 <b>Video havolasi</b>\n\nYouTube, Instagram yoki Facebook havolasini yuboring, men uni yuklab beraman! 📥",
        "round_video_prompt": "⭕️ <b>Dumaloq video</b>\n\nOddiy videoni yuboring, men uni dumaloq videoga aylantirib beraman. 📹",
        "converting_round": "🔄 Dumaloq videoga aylantirilmoqda...",
        "round_video_error": "⚠️ Dumaloq videoga aylantirishda xatolik.",
        "back_to_video": "📹 Video bo'limiga",
        "profile_header": "<b>👤 Profil ma'lumotlaringiz:</b>",
        "profile_not_found": "Profil topilmadi.",
        "not_found": "😔 Hech narsa topilmadi. Boshqa so'z bilan urinib ko'ring.",
        "welcome_ready": "Salom, {name}! 👋\nSizga qanday yordam bera olaman? Kerakli xizmatni tanlang: 👇",
        "my_music": "🎵 Musiqalarim",
        "save_music": "💾 Saqlash",
        "save_video": "💾 Videoni saqlash",
        "music_saved": "✅ Saqlandi",
        "download_in_progress_alert": "⚠️ Hozirda yuklash jarayoni ketmoqda!\nIltimos, biroz kuting.",
        "music_download_error_external": "Kechirasiz, ushbu musiqani yuklashda xatolik bo'ldi. Boshqa musiqani yuklab ko'ring.",
        "file_too_large": "⚠️ Kechirasiz, ushbu fayl hajmi juda katta. Boshqa musiqani yuklab ko'ring.",
        "downloaded_via_bot": "🤖 @{bot_username} orqali yuklandi",
        "converted_via_bot": "🤖 @{bot_username} orqali o'girildi",
        "saved_via_bot": "🎵 <b>{title}</b>\n\n🤖 @{bot_username} orqali saqlab olingan",
        "video_saved_via_bot": "📹 <b>{title}</b>\n\n🤖 @{bot_username} orqali saqlab olingan",
        "music_almost_ready": "Musiqa deyarli tayyor bo'lib qoldi. Sabr-toqatingiz uchun rahmat! ⏳",
        "music_saved_alert": "Musiqa saqlandi! ✅\nUni ko'rish uchun 'Musiqalarim' bo'limiga o'ting.",
        "video_saved_alert": "Video saqlandi! ✅\nUni ko'rish uchun 'Saqlangan videolar' tugmasini bosing.",
        "music_already_saved": "✅ Avval saqlangan",
        "image_already_saved": "✅ Rasm avval saqlangan",
        "video_already_saved": "✅ Ushbu video allaqachon saqlangan",
        "my_music_list_header_delete": "🎵 <b>Saqlangan musiqalaringiz ({count} dona):</b>\n\n<i>Musiqani tinglash uchun quyidagi tugmalardan birini bosing:</i>",
        "my_video_list_header_elete": "📹 <b>Saqlangan videolaringiz:</b>\n\n<i>Ko'rish uchun raqamni bosing.</i>",
        "no_saved_music": "😔 Sizda saqlangan musiqalar yo'q.\n\n<i>Musiqa yuklaganingizdan so'ng 'Saqlash' tugmasini bosing.</i>",
        "no_saved_videos": "😔 Sizda saqlangan videolar yo'q.\n\n<i>Video yuklaganingizdan so'ng 'Saqlash' tugmasini bosing.</i>",
        "back_to_music": "⬅️ Musiqa menyusiga",
        "enter_music_query_extended": "🎵 Qo'shiq nomini yoki ijrochi ismini kiriting:\n\n⚠️ <i>Iltimos, musiqa yoki ijrochi nomini to'g'ri kiritishga harakat qiling. Agar xato yozsangiz, noto'g'ri natija chiqishi mumkin.</i>",
        "converting_video": "📥 Video MP3 formatiga o'girilmoqda...",
        "conversion_error": "⚠️ Videoni MP3'ga o'girishda xatolik.",
        "video_deleted": "🗑 Video o'chirildi.",
        "text_to_voice_btn": "📝 Matn -> Ovoz",
        "voice_to_text_only_btn": "🗣 Ovoz -> Matn",
        "tts_send_next": "Yana matn yuborishingiz mumkin.",
        "text_to_voice_prompt": "📝 <b>Matnni ovozga aylantirish</b>\n\nMatnni yozib yuboring, men uni ovozli xabar qilib beraman. 🗣",
        "admin_welcome": "Admin panelga xush kelibsiz! 🔧",
        "lbl_username": "👤 Foydalanuvchi nomi",
        "lbl_name": "👤 Ism va familya",
        "lbl_region": "🏢 Viloyat",
        "lbl_district": "💒 Tuman",
        "lbl_neighborhood": "🏡 Mahalla",
        "lbl_phone": "📲 Telefon",
        "lbl_address": "📍 Manzil",
        "lbl_map": "Xaritada ko'rish",
        "lbl_none": "Yo'q",
        "btn_delete_profile": "🗑️ Profilni o'chirish", # noqa
        "btn_create_profile": "➕ Profil yaratish",
        "btn_restore_profile": "🔄 Profilni tiklash",
        "privacy_notice": "🔒 <b>Hurmatli foydalanuvchi!</b>\n\nSizning profil ma'lumotlaringiz begonalarga ko'rsatilmaydi. Maxfiylik va xavfsizlik to'liq ta'minlanadi. ✅",
        "about_text": "🤖 <b>Dono Bot — Sizning universal yordamchingiz!</b>\n\nBu bot kundalik yumushlaringizni osonlashtirish uchun mo'ljallangan:\n\n📥 <b>Media yuklovchi:</b> YouTube, Instagram va Facebook'dan videolarni yuklab oling.\n🎵 <b>Musiqa olami:</b> Musiqa qidiring, videodan audio ajrating va Shazam orqali aniqlang.\n🗣 <b>Ovozli xizmatlar:</b> Matnni ovozga va ovozli xabarni matnga aylantiring.\n🖼 <b>Rasm tahrirlovchi:</b> Fonni olib tashlang va filtrlar qo'llang.\n🔄 <b>Professional tarjimon:</b> O'zbek, Rus va Ingliz tillari o'rtasida tarjima qiling.\n📢 <b>Reklama xizmati:</b> Mahsulotingizni bot orqali taniting.\n🆘 <b>Jonli muloqot:</b> Muammolar bo'yicha adminlar bilan bog'laning.\n\n🔒 <b>Xavfsizlik:</b> Ma'lumotlaringiz maxfiy saqlanadi.",
        "error": "⚠️ Xatolik yuz berdi.",
        "msg_wait_admin": "Xabaringiz adminga yuborildi, javobni kuting. ⏳",
        "rate_bot": "Iltimos, botni baholang (1-5): ⭐",
        "write_feedback": "Fikr va takliflaringizni yozib qoldiring: 📝\n(Matn, rasm yoki video yuborishingiz mumkin)",
        "feedback_received_return_main": "Fikr va taklifingiz uchun rahmat! ✅",
        "order_deleted": "Buyurtma o'chirildi! 🗑️",
        "chat_ended_rate": "Chat yakunlandi. 🏁\nIltimos, xizmat sifatini baholang:",
        "support_request_sent": "Qo'llab-quvvatlash so'rovingiz yuborildi. Admin javobini kuting. ⏳",
        "admin_joined_chat": "✅ Admin sizning so'rovingizni qabul qildi! 💬\nEndi suhbatlashishingiz mumkin.",
        "admin_rejected_chat": "❌ Admin so'rovingizni rad etdi. Keyinroq urinib ko'ring.",
        "chat_ended_user": "Foydalanuvchi chatni yakunladi. ❌",
        "search_results_header": "🎵 <b>Qidiruv natijalari ({page}-sahifa):</b>",
        "insta_downloading": "📥 Instagram'dan video yuklanmoqda...",
        "generic_downloading": "📥 Video yuklanmoqda...",
        "users_excel_btn": "📥 Foydalanuvchilar (Excel)",
        "admin_users_count": "👥 <b>Jami foydalanuvchilar:</b> {count} ta\n\nBoshqarish uchun foydalanuvchi tartib raqamini yuboring.\n\n",
        "edit_profile_prompt": "<b>Qaysi qismni tahrirlamoqchisiz?</b> ✏️",
        "enter_new_fullname": "Yangi <b>ism va familyangizni</b> kiriting: 👤",
        "enter_new_region": "Yangi <b>viloyatni</b> tanlang: 🌍",
        "yt_video_loading": "📥 YouTube'dan video yuklanmoqda...",
        "yt_video_processing": "📥 Video qayta ishlanmoqda... Iltimos, biroz kuting. ⏳",
        "yt_downloading_res": "📥 {resolution}p sifatda yuklanmoqda... Biroz kuting.",
        "enter_new_district": "Yangi <b>tumanni</b> tanlang: 🏘️",
        "enter_new_district_input": "Yangi <b>tumanni</b> kiriting: 🏘️",
        "enter_new_neighborhood": "Yangi <b>mahallani</b> tanlang: 🏠",
        "enter_new_neighborhood_input": "Yangi <b>mahallani</b> kiriting: 🏠",
        "enter_new_phone": "Yangi <b>telefon raqamingizni</b> kiriting: 📞",
        "enter_new_location": "Yangi <b>joylashuvingizni</b> ulashing: 📍",
        "editing_mode": "Tahrirlash rejimi! ✏️",
        "yt_video_found": "📹 <b>YouTube videosi topildi!</b>\nIltimos, formatni tanlang:",
        "choose_video_quality": "🎥 <b>Video sifatini tanlang:</b>",
        "fmt_mp3": "🎵 MP3 (Audio)",
        "fmt_video": "🎬 Video (MP4)",
        "my_videos": "📹 Videolarim",
        "my_images": "🖼 Rasmlarim",
        "search_btn": "🔍 Qidirish",
        "page_label": "📄 Sahifa",
        "profile_updated": "Profil muvaffaqiyatli yangilandi! ✅",
        "btn_end_chat": "❌ Chatni yakunlash",
        "confirm_delete_profile": "Haqiqatdan ham profilni o'chirmoqchimisiz? ⚠️",
        "yes": "✅ Ha",
        "no": "❌ Yo'q",
        "profile_deleted": "Profil o'chirildi! 🗑️",
        "action_cancelled": "Bekor qilindi! ❌",
        "cancelled_text": "Bekor qilindi. ❌",
        "admin_not_admin": "Siz admin emassiz! ❌",
        "user_is_banned": "🚫 {name}, siz bloklangansiz! Botdan foydalana olmaysiz.",
        "user_is_banned_alert": "🚫 {name}, siz bloklangansiz!",
        "admin_no_banned_users": "Bloklangan foydalanuvchilar yo'q.",
        "admin_no_users": "Foydalanuvchilar yo'q.",
        "user_not_found": "Foydalanuvchi topilmadi.",
        "admin_user_id_not_found": "Ushbu ID bo'yicha foydalanuvchi topilmadi. 🤷‍♂️",
        "admin_enter_valid_user_id": "Iltimos, to'g'ri foydalanuvchi ID'sini kiriting (faqat raqamlar).",
        "excel_preparing": "Fayl tayyorlanmoqda, iltimos kuting...",
        "excel_no_users": "Yuklab olish uchun <b>foydalanuvchilar yo'q.</b>",
        "excel_error": "Excel faylini yaratishda <b>xatolik yuz berdi.</b>",
        "bot_token_missing": "BOT_TOKEN topilmadi! .env faylini tekshiring.",
        "bot_started": "✅ Bot ishga tushdi!",
        "bot_start_error": "Bot ishga tushishda xato: {error}",
        "bot_stopped": "Bot to'xtatildi.",
        "bot_stopped_by_admin": "Bot admin tomonidan to'xtatildi.",
        "unexpected_error": "Kutilmagan xato: {error}",
        "already_in_chat": "Siz allaqachon chatdasiz. 💬",
        "request_already_processed": "So'rov allaqachon ishlov berilgan. ⚠️",
        "chat_activated": "Chat faollashtirildi! 💬\nFoydalanuvchi bilan suhbatlashish mumkin.\nYakunlash uchun tugmani bosing 👇",
        "chat_accepted": "Chat qabul qilindi! ✅",
        "feedback_thank_you_full": "Rahmat fikr taklifingiz uchun biz sizning fikr taklifingizni qadrlaymiz! ✅",
        "admin_users_list": "📋 <b>Foydalanuvchilar ro'yxati:</b>",
        "admin_back": "⬅️ Admin panelga",
        "admin_action_block": "🚫 Bloklash",
        "admin_action_unblock": "✅ Blokdan chiqarish",
        "admin_action_notify": "📩 Xabar yuborish",
        "user_blocked_by_admin": "🚫 {name}, siz admin tomonidan <b>bloklandingiz</b>. Agar buni xatolik deb hisoblasangiz, biz bilan bog'lanishingizni so'rab qolamiz.",
        "admin_user_blocked": "Foydalanuvchi bloklandi! 🚫",
        "admin_user_unblocked": "Foydalanuvchi blokdan chiqarildi! ✅",
        "admin_enter_notify": "Foydalanuvchiga yuboriladigan xabarni kiriting:",
        "admin_notify_sent": "Xabar yuborildi! ✅",
        "admin_grant_admin": "👑 Admin qilish",
        "admin_revoke_admin": "⬇️ Adminlikdan olish",
        "admin_grant_special": "🌟 Maxsus ruxsat berish",
        "admin_revoke_special": "❌ Maxsus ruxsatni olish",
        "select_voice_gender": "🗣 <b>Ovoz turini tanlang:</b>",
        "voice_male": "👨 Erkak",
        "voice_female": "👩 Ayol",
        "profile_restored_success": "Profil muvaffaqiyatli tiklab olindi! ✅",
        "converting_to_voice": "🗣 <b>Ovozga aylantirilmoqda...</b> ⏳",
        "file_too_large_for_processing": "⚠️ Kechirasiz, fayl hajmi ruxsat etilgan miqdordan katta. Iltimos, kichikroq fayl yuboring.",
        "send_voice_or_audio": "🗣 <b>Ovoz -> Matn</b>\n\nOvozli xabar yoki audio fayl yuboring.",
        "music_limit_50mb_alert": "⚠️ Kechirasiz {name}, ushbu musiqa hajmi 50MB dan oshadi. Iltimos, boshqa musiqa yuklang.",
        "profile_joined_date": "Qo'shilgan sana",
        "profile_days_count": "Bot bilan birga",
        "user_unblocked_alert": "✅ {name}, siz blokdan chiqarildingiz! Botdan qayta foydalanishingiz mumkin.",
        "welcome_ads_name": "{name}, reklama bo'limiga xush kelibsiz! 📢\nBu yerda o'z mahsulot yoki xizmatlaringizni bizning platformamiz orqali keng ommaga tanitishingiz mumkin. Marhamat, kerakli xizmat turini tanlang 👇",
        "welcome_music_name": "{name}, musiqa olamiga xush kelibsiz! 🎵\nBu yerda siz musiqa qidirishingiz, saqlanganlaringizni tinglashingiz va boshqa audio amallarni bajarishingiz mumkin. 👇",
        "welcome_video_name": "{name}, video bo'limiga xush kelibsiz! 📹\nIjtimoiy tarmoqlardan videolarni yuklab oling yoki videolarni dumaloq shaklga keltiring. Marhamat 👇",
        "welcome_image_name": "{name}, rasm bo'limiga xush kelibsiz! 🖼\nRasmlaringiz fonini oson olib tashlang yoki ularga turli effektlar bering. Kerakli amalni tanlang 👇",
        "feedback_welcome_name": "{name}, fikr va takliflar bo'limiga xush kelibsiz! 💬\nFikr va takliflaringizni yozib qoldiring: 📝",
        "shazam_prompt": "🎵 <b>Shazam xizmati</b>\n\nQisqa audio yoki videoni yuboring. Men uni tinglab, musiqani topib beraman! 🎧",
        "shazam_recognizing": "🎧 <b>Eshitmoqdaman...</b> ⏳",
        "btn_find_music": "🎵 Musiqasini topish (Shazam)",
        "get_audio_from_video": "🎵 Musiqasini olish (Audio)",
        "shazam_not_found": "😔 Kechirasiz, bu musiqani taniy olmadim.",
        "shazam_found_downloading": "🎵 <b>{title} - {artist}</b> topildi.\n📥 Musiqangiz yuklanmoqda, iltimos biroz kuting. Sabr-toqatingiz uchun rahmat!",
        "audio_received_saved": "✅ Audio qabul qilindi va 'Musiqalarim' ro'yxatiga qo'shildi.",
        "video_received_saved": "✅ Video qabul qilindi va 'Videolarim' ro'yxatiga qo'shildi.",
        "processed_via_bot": "🤖 @{bot_username} orqali qayta ishlandi",
        "image_saved_alert": "Rasm saqlandi! ✅",
        "no_saved_images": "😔 Sizda saqlangan rasmlar yo'q.",
        "my_images_list_header": "🖼 <b>Saqlangan rasmlaringiz:</b>\n\n<i>Ko'rish uchun raqamni bosing.</i>",
        "image_deleted": "Rasm o'chirildi! 🗑️",
        "search_music_prompt": "🎵 Qidirayotgan musiqangiz nomini yozing:",
        "search_results": "🔍 <b>Qidiruv natijalari ({count} ta):</b>",
        "phone_error": "⚠️ Iltimos, to'g'ri telefon raqam kiriting (9 xona).\nMasalan: 901234567",
        "share_phone": "📱 Telefon raqamni ulashish",
        "session_expired": "⏳ Sessiya vaqti tugadi. Qayta boshlash uchun /start bosing.",
        "old_button": "⚠️ Bu tugma eskirgan. Iltimos, /start buyrug‘ini qayta yuboring.",
        "enter_phone_prompt": "Telefon raqamingizni yuboring yoki quyidagi tugmani bosing: 📞",
        "enter_district_prompt": "Tumanni kiriting yoki tanlang: 🏘️",
        "session_expired_alert": "Tugmalar muddati tugagan. 🔄\nQayta boshlash uchun /start bosing.",
        "admin_notify_flood": "⚠️ <b>Flood Ogohlantirish!</b>\n👤 Foydalanuvchi: {user}\n🆔 ID: {user_id}\n📝 Sabab: /start spam (Tezkor harakat)",
        "admin_notify_captcha_ban": "⚠️ <b>Xavfsizlik Ban!</b>\n👤 Foydalanuvchi: {user}\n🆔 ID: {user_id}\n📝 Sabab: Captcha xatosi",
        "enter_neighborhood_prompt": "Mahallani kiriting: 🏠",
        "btn_edit_profile": "✏️ Profilni tahrirlash",
        "captcha_fail_attempts": "❌ <b>Xato javob!</b>\n\nQolgan urinishlar soni: <b>{attempts}</b> ta.\n\nYangi misol: <b>{challenge} = ?</b>",
        "select_district_prompt": "Tumanni tanlang: 🏘️",
        "select_neighborhood_prompt": "Mahallani tanlang: 🏠",
        "admin_orders_list": "🛒 Buyurtmalar ro'yxati",
        "admin_search_user": "🔍 Foydalanuvchi qidirish",
        "profile_security_header": "Profil havfsizligi:",
        "profile_security_safe": "✅ 🔒 Profilingiz havfsiz holatda",
        "profile_security_warning": "⚠️ Profilingiz havfsizligida muammo bor",
        "music_search_btn": "🔍 Musiqa qidirish",
        "shazam_btn": "🎵 Shazam (Musiqa topish)",
    },
    "ru": {
        "translate": "🔄 Перевод",
        "translate_in_development": "Эта функция в настоящее время находится в разработке. Пожалуйста, подождите!",
        "select_source_language": "С какого языка вы хотите перевести?",
        "welcome_main": "Добро пожаловать в главное меню! 🌟",
        "ads": "📢 Раздел рекламы",
        "new_ad_order_admin": "🆕 Вам поступил заказ на рекламу: {order_id}\nПожалуйста, проверьте раздел 'Заказы' в админ панели.",
        "music": "🎵 Раздел музыки",
        "music_search_btn": "🔍 Поиск музыки",
        "shazam_btn": "🎵 Shazam (Найти музыку)",
        "my_videos": "📹 Мои видео",
        "my_images": "🖼 Мои картинки",
        "support": "🆘 Поддержка",
        "image_section": "🖼 Раздел картинок",
        "btn_remove_bg": "✂️ Удалить фон",
        "btn_filter": "🎨 Изменить цвет (Ч/Б)",
        "profile_daily_stats": "\n\n—\n📊 <b>Статистика за сегодня:</b>\n📥 Всего загрузок: {count}",
        "send_photo_bg": "Отправьте фото для удаления фона 📤",
        "send_photo_filter": "Отправьте фото, я сделаю его чёрно-белым 📤",
        "save_image": "💾 Сохранить",
        "processing_image": "🖼 Обработка изображения... Пожалуйста, подождите ⏳",
        "back_to_images": "⬅️ В раздел картинок",
        "rembg_not_installed": "⚠️ Библиотека 'rembg' не установлена на сервере.",
        "generic_downloading": "📥 Видео загружается...",
        "profile_status_excellent": "✅ {name}, ваш профиль полный и отличный! Вам 5 баллов!",
        "profile_header_admin": "<b>📋 Данные профиля пользователя:</b>",
        "ads_choose_type": "Каким типом рекламы хотите воспользоваться? 👇",
        "ads_social": "📱 Реклама в соцсетях",
        "feedback": "💬 Отзывы",
        "profile_status_header": "\n\n—\n📊 <b>Статус профиля</b>\n",
        "profile_status_good": "👍 {name}, ваш профиль почти полон. Вам <b>4 балла</b>.",
        "profile_status_satisfactory": "😐 {name}, ваш профиль в удовлетворительном состоянии. Вам <b>3 балла</b>. Рекомендуем заполнить недостающие данные.",
        "profile_status_poor": "😕 {name}, в вашем профиле мало информации. Вам <b>2 балла</b>. Пожалуйста, заполните свой профиль.",
        "profile_status_very_poor": "👎 {name}, ваш профиль пуст. Вам <b>1 балл</b>. Пожалуйста, введите данные через кнопку 'Редактировать'.",
        "about": "ℹ️ О боте",
        "profile": "👤 Профиль",
        "admin": "🔰 Админ панель",
        "settings": "⚙️ Настройки",
        "share_location": "📍 Поделиться местоположением",
        "back_main": "🏠 Главное меню",
        "select_lang": "Выберите язык:",
        "save": "💾 Сохранить",
        "saved": "Сохранено! ✅",
        "cancel": "❌ Отмена",
        "selected": "Выбрано: {l_name}",
        "lang_uz": "🇺🇿 O'zbekcha",
        "lang_ru": "🇷🇺 Русский",
        "lang_en": "🇬🇧 English",
        "select_target_language": "На какой язык вы хотите перевести?",
        "enter_text_for_translation": "Введите текст для перевода:",
        "searching_music": "🔍 Поиск музыки... Пожалуйста, подождите.",
        "press_to_download": "⬇️ <i>Нажмите на номер ниже для скачивания:</i>",
        "btn_prev_page": "⬅️ Назад",
        "btn_next_page": "Вперёд ➡️",
        "music_download_wait": "📥 Музыка загружается... Пожалуйста, подождите, спасибо за терпение.",
        "temp_blocked": "🚫 {name}, вы временно заблокированы!\n⏳ Подождите {wait_time} мин.",
        "delete_all": "🗑 Удалить все",
        "confirm_delete_all_videos": "⚠️ <b>Внимание!</b>\n\nВы действительно хотите удалить все сохраненные видео?",
        "deleted_all_videos_restore": "🗑 <b>Вы удалили все видео.</b>\n\nХотите их восстановить?",
        "btn_restore": "♻️ Восстановить",
        "all_restored": "Все восстановлено! ✅",
        # Admin
        "ads_simple_text": "📝 Простая текстовая реклама",
        "ads_choose_platform": "В какой социальной сети вы хотите разместить рекламу? 👇",
        "ads_platform_insta": "📸 Instagram",
        "ads_platform_tg": "✈️ Telegram",
        "ads_platform_all": "🌐 Во всех сетях",
        "ads_enter_text": "Пожалуйста, введите текст рекламы и укажите необходимую информацию: 📝",
        "ads_ask_media": "Есть ли у вас файл или медиа для прикрепления? 📎",
        "ads_send_media": "Пожалуйста, отправьте медиафайл (Фото или Видео): 📤",
        "ads_confirm_title": "📋 <b>Подтверждение заказа:</b>\nПожалуйста, проверьте данные:",
        "ads_btn_confirm": "✅ Подтвердить",
        "ads_btn_edit": "✏️ Редактировать",
        "ads_btn_cancel": "❌ Отменить",
        "ads_order_sent": "✅ {name}, ваш заказ принят! Наши администраторы свяжутся с вами в ближайшее время.",
        "ads_edit_what": "Что вы хотите отредактировать?",
        "ads_edit_platform": "📱 Изменить соцсеть",
        "ads_edit_media": "📷 Изменить медиа",
        "ads_edit_text": "📝 Изменить текст",
        "ads_save_changes": "Сохранить новые данные? 💾",
        "ads_saved": "Изменения сохранены! ✅",
        "order_status_completed_msg": "Уважаемый пользователь! Ваш заказ рассмотрен. Ожидайте связи с нашими специалистами. ✅",
        "order_status_later_msg": "Уважаемый пользователь! Ваш заказ находится на стадии рассмотрения. Спасибо, что выбрали нас! ⏳",
        "btn_completed": "✅ Выполнено",
        "btn_later": "⏳ Позже",
        "ads_type_social": "Соцсети",
        "ads_type_simple": "Простой текст",
        "voice_to_text_btn": "🗣 Конвертер голоса и текста",
        "video_to_mp3_btn": "📹 Видео в MP3",
        "voice_to_text_prompt": "🗣 <b>Конвертер голоса и текста</b>\n\nВыберите услугу: 👇",
        "video_to_mp3_prompt": "📹 <b>Видео в MP3</b>\n\nОтправьте любое видео, и я конвертирую его в аудио (MP3). 🎵",
        "video_section": "📹 Раздел видео",
        "round_video_btn": "⭕️ Круглое видео",
        "video_link_prompt_extended": "🔗 <b>Ссылка на видео</b>\n\nОтправьте ссылку на YouTube, Instagram или Facebook, и я скачаю видео! 📥",
        "video_link_btn": "🔗 Ссылка на видео",
        "round_video_prompt": "⭕️ <b>Круглое видео</b>\n\nОтправьте обычное видео, и я сделаю из него круглое видео. 📹",
        "converting_round": "🔄 Конвертация в круглое видео...",
        "round_video_error": "⚠️ Ошибка при создании круглого видео.",
        "back_to_video": "📹 В раздел видео",
        "profile_header": "<b>📋 Ваши данные профиля:</b>",
        "profile_not_found": "Профиль не найден.",
        "not_found": "😔 Ничего не найдено. Попробуйте другой запрос.",
        "welcome_ready": "Привет, {name}! 👋\nЯ готов к работе. Выберите нужное действие: 👇",
        "my_music": "🎵 Моя музыка",
        "save_music": "💾 Сохранить",
        "save_video": "💾 Сохранить",
        "music_saved": "✅ Сохранено",
        "download_in_progress_alert": "⚠️ Загрузка уже идет!\nПожалуйста, подождите.",
        "music_download_error_external": "Извините, произошла ошибка при загрузке. Попробуйте другую музыку.",
        "file_too_large": "Извините, файл слишком большой (лимит Telegram). Попробуйте другую музыку.",
        "yt_video_loading": "📥 Загружается видео с YouTube...",
        "yt_video_processing": "📥 Видео обрабатывается... Пожалуйста, подождите. ⏳",
        "downloaded_via_bot": "🤖 Загружено через @{bot_username}",
        "converted_via_bot": "🤖 Конвертировано через @{bot_username}",
        "saved_via_bot": "🎵 <b>{title}</b>\n\n🤖 Сохранено через @{bot_username}",
        "video_saved_via_bot": "📹 <b>{title}</b>\n\n🤖 Сохранено через @{bot_username}",
        "music_almost_ready": "Музыка почти готова. Спасибо за ваше терпение! ⏳",
        "music_saved_alert": "Музыка сохранена! ✅\nЧтобы просмотреть, нажмите кнопку 'Моя музыка' в разделе Музыка.",
        "video_saved_alert": "Видео сохранено! ✅\nЧтобы просмотреть, перейдите в раздел 'Мои видео'.",
        "music_already_saved": "✅ Уже сохранено",
        "image_already_saved": "✅ Картинка уже сохранена",
        "video_already_saved": "✅ Видео уже сохранено",
        "my_music_list_header_delete": "🎵 <b>Ваша сохраненная музыка ({count} шт.):</b>\n\n<i>Отправьте номер для прослушивания (например: <b>1</b>).</i>",
        "my_video_list_header_delete": "📹 <b>Ваши сохраненные видео:</b>\n\n<i>Нажмите на номер для просмотра.</i>",
        "no_saved_music": "😔 У вас нет сохраненной музыки.\n\n<i>Нажмите 'Сохранить' после загрузки музыки.</i>",
        "no_saved_videos": "😔 У вас нет сохраненных видео.\n\n<i>Нажмите 'Сохранить' после загрузки видео.</i>",
        "back_to_music": "⬅️ В меню музыки",
        "enter_music_query_extended": "🎵 Введите название песни или исполнителя:\n\n⚠️ <i>Пожалуйста, вводите название песни или исполнителя правильно. Ошибки в названии могут привести к неверным результатам.</i>",
        "converting_video": "📥 Конвертирую видео в MP3...",
        "conversion_error": "⚠️ Ошибка при конвертации видео в MP3.",
        "video_deleted": "🗑 Видео удалено.",
        "text_to_voice_btn": "📝 Текст -> Голос",
        "voice_to_text_only_btn": "🗣 Голос -> Текст",
        "tts_send_next": "Можете отправить следующий текст.",
        "text_to_voice_prompt": "📝 <b>Текст в голос</b>\n\nОтправьте текст, и я озвучу его. 🗣",
        "lbl_username": "👤 Имя пользователя",
        "lbl_name": "👤 Имя и фамилия",
        "lbl_region": "🏢 Область",
        "lbl_district": "💒 Район",
        "lbl_neighborhood": "🏡 Махалля",
        "lbl_phone": "📲 Телефон",
        "lbl_address": "📍 Адрес",
        "lbl_map": "Показать на карте",
        "lbl_none": "Нет",
        "btn_edit_profile": "✏️ Редактировать",
        "btn_delete_profile": "🗑️ Удалить",
        "btn_create_profile": "➕ Создать профиль",
        "btn_restore_profile": "🔄 Восстановить",
        "privacy_notice": "🔒 <b>Уважаемый пользователь!</b>\n\nВаши данные профиля не будут переданы третьим лицам. Конфиденциальность и безопасность гарантированы. ✅",
        "about_text": "🤖 <b>Dono Bot — Ваш универсальный помощник!</b>\n\nЭтот бот создан для упрощения ваших повседневных задач:\n\n📥 <b>Загрузчик медиа:</b> Скачивайте видео и аудио из YouTube, Instagram и Facebook.\n🎵 <b>Мир музыки:</b> Ищите музыку, извлекайте аудио из видео и распознавайте треки через Shazam.\n🗣 <b>Голосовые услуги:</b> Преобразуйте текст в речь и голосовые сообщения в текст.\n🖼 <b>Редактор изображений:</b> Удаляйте фон и применяйте фильтры.\n🔄 <b>Профессиональный переводчик:</b> Переводите тексты между UZ, RU и EN.\n📢 <b>Рекламные услуги:</b> Продвигайте свои товары через бота.\n🆘 <b>Живое общение:</b> Связывайтесь с администраторами.\n\n🔒 <b>Безопасность:</b> Все ваши данные конфиденциальны.",
        "error": "⚠️ Произошла ошибка.",
        "msg_wait_admin": "Ваше сообщение отправлено администратору, ожидайте ответа. ⏳",
        "rate_bot": "Пожалуйста, оцените бота (1-5): ⭐",
        "write_feedback": "Оставьте свои отзывы и предложения: 📝\n(Вы можете отправить текст, фото или видео)",
        "feedback_received_return_main": "Спасибо за ваш отзыв и предложение! ✅",
        "order_deleted": "Заказ удален! 🗑️",
        "chat_ended_rate": "Чат завершен. 🏁\nПожалуйста, оцените качество обслуживания:",
        "support_request_sent": "Ваш запрос в поддержку отправлен. Ожидайте ответа администратора. ⏳",
        "admin_joined_chat": "✅ Администратор принял ваш запрос! 💬\nТеперь вы можете общаться.",
        "admin_rejected_chat": "❌ Администратор отклонил ваш запрос. Попробуйте позже.",
        "chat_ended_user": "Пользователь завершил чат. ❌",
        "search_results_header": "🎵 <b>Результаты поиска (Страница {page}):</b>",
        "insta_downloading": "📥 Загружается видео из Instagram...",
        "edit_profile_prompt": "Какую часть вы хотите отредактировать? ✏️",
        "enter_new_fullname": "Введите новые имя и фамилию: 👤",
        "enter_new_region": "Выберите новую область: 🌍",
        "enter_new_district": "Выберите новый район: 🏘️",
        "enter_new_district_input": "Введите новый район: 🏘️",
        "enter_new_neighborhood": "Выберите новую махаллю: 🏠",
        "enter_new_neighborhood_input": "Введите новую махаллю: 🏠",
        "enter_new_phone": "Введите новый номер телефона: 📞",
        "enter_new_location": "Поделитесь новым местоположением: 📍",
        "editing_mode": "Режим редактирования! ✏️",
        "yt_video_found": "📹 <b>Найдено видео YouTube!</b>\nПожалуйста, выберите формат:",
        "choose_video_quality": "🎥 <b>Выберите качество видео:</b>",
        "yt_downloading_res": "📥 Загрузка в качестве {resolution}p... Пожалуйста, подождите.",
        "fmt_mp3": "🎵 MP3 (Аудио)",
        "fmt_video": "🎬 Видео (MP4)",
        "profile_updated": "Профиль успешно обновлен! ✅",
        "btn_end_chat": "❌ Завершить чат",
        "confirm_delete_profile": "Вы действительно хотите удалить свой профиль? ⚠️",
        "yes": "✅ Да",
        "no": "❌ Нет",
        "profile_deleted": "Профиль удален! 🗑️",
        "action_cancelled": "Отменено! ❌",
        "cancelled_text": "Отменено. ❌",
        "admin_not_admin": "Вы не администратор! ❌",
        "user_is_banned": "🚫 {name}, вы заблокированы! Вы не можете использовать бота.",
        "bot_token_missing": "BOT_TOKEN не найден! Проверьте файл .env.",
        "bot_started": "✅ Бот запущен!",
        "bot_start_error": "Ошибка при запуске бота: {error}",
        "bot_stopped": "Бот остановлен.",
        "bot_stopped_by_admin": "Бот остановлен администратором.",
        "unexpected_error": "Непредвиденная ошибка: {error}",
        "already_in_chat": "Вы уже в чате. 💬",
        "request_already_processed": "Запрос уже обработан. ⚠️",
        "chat_activated": "Чат активирован! 💬\nМожно общаться с пользователем.\nНажмите кнопку, чтобы завершить 👇",
        "chat_accepted": "Чат принят! ✅",
        "feedback_thank_you_full": "Спасибо за ваш отзыв, мы ценим ваше мнение! ✅",
        "select_voice_gender": "🗣 <b>Выберите тип голоса:</b>",
        "voice_male": "👨 Мужской",
        "voice_female": "👩 Женский",
        "profile_restored_success": "Профиль успешно восстановлен! ✅",
        "converting_to_voice": "🗣 <b>Конвертация в голос...</b> ⏳",
        "file_too_large_for_processing": "⚠️ К сожалению, размер файла превышает допустимый лимит. Пожалуйста, отправьте файл меньшего размера.",
        "send_voice_or_audio": "🗣 <b>Голос -> Текст</b>\n\nОтправьте голосовое сообщение или аудиофайл.",
        "music_limit_50mb_alert": "⚠️ Извините {name}, размер этой музыки превышает 50 МБ. Пожалуйста, загрузите другую музыку.",
        "profile_joined_date": "Дата присоединения",
        "profile_days_count": "Вместе с ботом",
        "user_unblocked_alert": "✅ {name}, вы разблокированы! Вы можете снова использовать бота.",
        "welcome_ads_name": "{name}, добро пожаловать в раздел рекламы! 📢\nЗдесь вы можете продвигать свои товары или услуги широкой аудитории через нашу платформу. Пожалуйста, выберите тип услуги 👇",
        "welcome_music_name": "{name}, добро пожаловать в раздел музыки! 🎵\nЗдесь вы можете искать музыку, слушать сохраненные треки и выполнять другие аудио операции. Пожалуйста, выберите нужную кнопку 👇",
        "welcome_video_name": "{name}, добро пожаловать в раздел видео! 📹\nЛегко скачивайте видео из соцсетей, таких как YouTube и Instagram, или превращайте свои видео в круглые. Пожалуйста 👇",
        "welcome_image_name": "{name}, добро пожаловать в раздел изображений! 🖼\nЛегко удаляйте фон с ваших фотографий или применяйте к ним различные эффекты. Выберите желаемое действие 👇",
        "feedback_welcome_name": "{name}, добро пожаловать в раздел отзывов! 💬\nОставьте свои отзывы и предложения: 📝",
        "get_audio_from_video": "🎵 Получить аудио",
        "btn_find_music": "🎵 Найти музыку (Shazam)",
        "shazam_prompt": "🎵 <b>Режим Shazam</b>\n\nПожалуйста, отправьте короткое аудио, голосовое сообщение или видео. Я послушаю его, найду музыку и скачаю её для вас! 🎧",
        "shazam_recognizing": "🎧 <b>Слушаю...</b> ⏳",
        "shazam_not_found": "😔 Извините, я не смог распознать эту музыку.",
        "shazam_found_downloading": "🎵 <b>{title} - {artist}</b> найден.\n📥 Ваша музыка загружается, пожалуйста, подождите. Спасибо за терпение!",
        "audio_received_saved": "✅ Аудио принято и добавлено в список 'Моя музыка'.",
        "video_received_saved": "✅ Видео принято и добавлено в список 'Мои видео'.",
        "processed_via_bot": "🤖 Обработано через @{bot_username}",
        "image_saved_alert": "Картинка сохранена! ✅",
        "no_saved_images": "😔 У вас нет сохраненных картинок.",
        "my_images_list_header": "🖼 <b>Ваши сохраненные картинки:</b>\n\n<i>Нажмите на номер для просмотра.</i>",
        "image_deleted": "Картинка удалена! 🗑️",
        "page_label": "📄 Страница",
        "search_btn": "🔍 Поиск",
        "search_music_prompt": "🎵 Введите название музыки для поиска:",
        "search_results": "🔍 <b>Результаты поиска ({count} шт.):</b>",
        "phone_error": "⚠️ Пожалуйста, введите правильный номер телефона (9 цифр).\nНапример: 901234567",
        "share_phone": "📱 Поделиться номером",
        "session_expired": "⏳ Время сессии истекло. Пожалуйста, нажмите /start.",
        "old_button": "⚠️ Кнопка устарела. Пожалуйста, отправьте /start.",
        "session_expired_alert": "Срок действия кнопок истек. 🔄\nПожалуйста, отправьте /start.",
        "enter_phone_prompt": "Отправьте свой номер телефона или нажмите кнопку ниже: 📞",
        "enter_district_prompt": "Введите название района: 🏘️",
        "enter_neighborhood_prompt": "Введите название махалли: 🏠",
        "captcha_fail_attempts": "❌ <b>Неверный ответ!</b>\n\nОсталось попыток: <b>{attempts}</b>.\n\nНовый пример: <b>{challenge} = ?</b>",
        "select_district_prompt": "Выберите район: 🏘️",
        "select_neighborhood_prompt": "Выберите махаллю: 🏠",
        "profile_security_header": "Безопасность профиля:",
        "profile_security_safe": "✅ 🔒 Ваш профиль в безопасном состоянии",
        "profile_security_warning": "⚠️ Проблема с безопасностью профиля",
    },
    "en": {
        "translate": "🔄 Translate",
        "translate_in_development": "This feature is currently under development. Please wait!",
        "select_source_language": "Which language do you want to translate from?",
        "welcome_main": "Welcome to the main menu! 🌟",
        "ads": "📢 Ads Section",
        "new_ad_order_admin": "🆕 You have a new ad order: {order_id}\nPlease check the 'Orders' section in the admin panel.",
        "music": "🎵 Music Section",
        "music_search_btn": "🔍 Search Music",
        "shazam_btn": "🎵 Shazam (Find Music)",
        "my_videos": "📹 My Videos",
        "my_images": "🖼 My Images",
        "support": "🆘 Support",
        "image_section": "🖼 Image Section",
        "btn_remove_bg": "✂️ Remove Background",
        "btn_filter": "🎨 Change color (B&W)",
        "profile_daily_stats": "\n\n—\n📊 <b>Today's Statistics:</b>\n📥 Total downloads: {count}",
        "send_photo_bg": "Send a photo to remove background 📤",
        "send_photo_filter": "Send a photo, I will convert it to black & white 📤",
        "save_image": "💾 Save",
        "processing_image": "🖼 Processing image... Please wait ⏳",
        "back_to_images": "⬅️ To Image Section",
        "rembg_not_installed": "⚠️ 'rembg' library is not installed on the server.",
        "generic_downloading": "📥 Downloading video...",
        "profile_status_excellent": "✅ {name}, your profile is complete and excellent! You get 5 points!",
        "profile_header_admin": "<b>📋 User profile details:</b>",
        "ads_choose_type": "What type of advertising service do you want to use? 👇",
        "ads_social": "📱 Social media ads",
        "feedback": "💬 Feedback",
        "profile_status_header": "\n\n—\n📊 <b>Profile Status</b>\n",
        "profile_status_good": "👍 {name}, your profile is almost complete. You get <b>4 points</b>.",
        "profile_status_satisfactory": "😐 {name}, your profile is in satisfactory condition. You get <b>3 points</b>. We recommend filling in the missing data.",
        "profile_status_poor": "😕 {name}, there is little information in your profile. You get <b>2 points</b>. Please complete your profile.",
        "profile_status_very_poor": "👎 {name}, your profile is empty. You get <b>1 point</b>. Please enter your data using the 'Edit' button.",
        "about": "ℹ️ About",
        "profile": "👤 Profile",
        "admin": "🔰 Admin Panel",
        "settings": "⚙️ Settings",
        "share_location": "📍 Share Location",
        "back_main": "🏠 Main Menu",
        "select_lang": "Select language:",
        "save": "💾 Save",
        "saved": "Saved! ✅",
        "cancel": "❌ Cancel",
        "selected": "Selected: {l_name}",
        "lang_uz": "🇺🇿 O'zbekcha",
        "lang_ru": "🇷🇺 Русский",
        "lang_en": "🇬🇧 English",
        "select_target_language": "Which language do you want to translate to?",
        "enter_text_for_translation": "Enter text for translation:",
        "searching_music": "🔍 Searching for music... Please wait.",
        "press_to_download": "⬇️ <i>Press the number below to download:</i>",
        "btn_prev_page": "⬅️ Back",
        "btn_next_page": "Next ➡️",
        "music_download_wait": "📥 Music is downloading... Please wait, thank you for your patience.",
        "temp_blocked": "🚫 {name}, you are temporarily blocked!\n⏳ Please wait {wait_time} minutes.",
        "delete_all": "🗑 Delete All",
        "confirm_delete_all_videos": "⚠️ <b>Warning!</b>\n\nDo you really want to delete all saved videos?",
        "deleted_all_videos_restore": "🗑 <b>You have deleted all videos.</b>\n\nDo you want to restore them?",
        "btn_restore": "♻️ Restore",
        "all_restored": "All restored! ✅",
        # Admin
        "ads_simple_text": "📝 Simple Text Ads",
        "ads_choose_platform": "Which social network do you want to advertise on? 👇",
        "ads_platform_insta": "📸 Instagram",
        "ads_platform_tg": "✈️ Telegram",
        "ads_platform_all": "🌐 All Networks",
        "ads_enter_text": "Please enter the ad text and provide necessary details: 📝",
        "ads_ask_media": "Do you have a file or media to attach? 📎",
        "ads_send_media": "Please send the media file (Photo or Video): 📤",
        "ads_confirm_title": "📋 <b>Confirm Order:</b>\nPlease check the details:",
        "ads_btn_confirm": "✅ Confirm",
        "ads_btn_edit": "✏️ Edit",
        "ads_btn_cancel": "❌ Cancel",
        "ads_order_sent": "✅ {name}, your order has been received! Our admins will contact you soon.",
        "ads_edit_what": "What do you want to edit?",
        "ads_edit_platform": "📱 Change Platform",
        "ads_edit_media": "📷 Change Media",
        "ads_edit_text": "📝 Change Text",
        "ads_save_changes": "Save new data? 💾",
        "ads_saved": "Changes saved! ✅",
        "order_status_completed_msg": "Dear user! Your order has been reviewed. Please wait for our specialists to contact you. ✅",
        "order_status_later_msg": "Dear user! Your order is under review. Thank you for choosing us! ⏳",
        "btn_completed": "✅ Completed",
        "btn_later": "⏳ Later",
        "ads_type_social": "Social Media",
        "ads_type_simple": "Simple Text",
        "voice_to_text_btn": "🗣 Voice & Text Converter",
        "video_to_mp3_btn": "📹 Video to MP3",
        "voice_to_text_prompt": "🗣 <b>Voice & Text Converter</b>\n\nChoose a service: 👇",
        "video_to_mp3_prompt": "📹 <b>Video to MP3</b>\n\nSend any video, and I will convert it to audio (MP3). 🎵",
        "video_section": "📹 Video Section",
        "round_video_btn": "⭕️ Round Video",
        "video_link_prompt_extended": "🔗 <b>Video Link</b>\n\nSend a YouTube, Instagram or Facebook link, and I will download it! 📥",
        "video_link_btn": "🔗 Video Link",
        "round_video_prompt": "⭕️ <b>Round Video</b>\n\nSend a normal video, and I will convert it to a round video. 📹",
        "converting_round": "🔄 Converting to round video...",
        "round_video_error": "⚠️ Error converting to round video.",
        "back_to_video": "📹 To Video Section",
        "profile_header": "<b>📋 Your Profile Details:</b>",
        "profile_not_found": "Profile not found.",
        "not_found": "😔 Nothing found. Try another query.",
        "welcome_ready": "Hello, {name}! 👋\nI am ready to work with you. Choose an action: 👇",
        "my_music": "🎵 My Music",
        "save_music": "💾 Save",
        "save_video": "💾 Save",
        "music_saved": "✅ Saved",
        "download_in_progress_alert": "⚠️ Download in progress!\nPlease wait.",
        "music_download_error_external": "Sorry, error downloading this music. Try another one.",
        "file_too_large": "Sorry, file is too large (Telegram limit). Try another one.",
        "yt_video_loading": "📥 Downloading video from YouTube...",
        "yt_video_processing": "📥 Video is being processed... Please wait. ⏳",
        "downloaded_via_bot": "🤖 Downloaded via @{bot_username}",
        "converted_via_bot": "🤖 Converted via @{bot_username}",
        "saved_via_bot": "🎵 <b>{title}</b>\n\n🤖 Saved via @{bot_username}",
        "video_saved_via_bot": "📹 <b>{title}</b>\n\n🤖 Saved via @{bot_username}",
        "music_almost_ready": "Music is almost ready. Thank you for your patience! ⏳",
        "music_saved_alert": "Music saved! ✅\nTo view it, click the 'My Music' button in the Music section.",
        "video_saved_alert": "Video saved! ✅\nTo view it, go to the 'My Videos' section.",
        "music_already_saved": "✅ Already saved",
        "image_already_saved": "✅ Image already saved",
        "video_already_saved": "✅ Video already saved",
        "my_music_list_header_delete": "🎵 <b>Your Saved Music ({count} items):</b>\n\n<i>Send a number to listen (e.g., <b>1</b>).</i>",
        "my_video_list_header_delete": "📹 <b>Your Saved Videos:</b>\n\n<i>Click a number to view.</i>",
        "no_saved_music": "😔 You have no saved music.\n\n<i>Press 'Save' after downloading a song.</i>",
        "no_saved_videos": "😔 You have no saved videos.\n\n<i>Press 'Save' after downloading a video.</i>",
        "back_to_music": "⬅️ To Music Menu",
        "enter_music_query_extended": "🎵 Enter song name or artist:\n\n⚠️ <i>Please try to enter the song or artist name correctly. Incorrect spelling may lead to wrong results.</i>",
        "converting_video": "📥 Converting video to MP3...",
        "conversion_error": "⚠️ Error converting video to MP3.",
        "video_deleted": "🗑 Video deleted.",
        "text_to_voice_btn": "📝 Text -> Voice",
        "voice_to_text_only_btn": "🗣 Voice -> Text",
        "tts_send_next": "You can send another text.",
        "text_to_voice_prompt": "📝 <b>Text to Voice</b>\n\nSend text, and I will convert it to voice. 🗣",
        "lbl_username": "👤 Username",
        "lbl_name": "👤 Full Name",
        "lbl_region": "🏢 Region",
        "lbl_district": "💒 District",
        "lbl_neighborhood": "🏡 Neighborhood",
        "lbl_phone": "📲 Phone",
        "lbl_address": "📍 Address",
        "lbl_map": "View on Map",
        "lbl_none": "None",
        "btn_edit_profile": "✏️ Edit",
        "btn_delete_profile": "🗑️ Delete",
        "btn_create_profile": "➕ Create Profile",
        "btn_restore_profile": "🔄 Restore Profile",
        "privacy_notice": "🔒 <b>Dear User!</b>\n\nYour profile data will not be shared with 3rd parties. Privacy and security are fully guaranteed. ✅",
        "about_text": "🤖 <b>Dono Bot — Your Universal Assistant!</b>\n\nThis bot is designed to simplify your daily tasks:\n\n📥 <b>Media Downloader:</b> Download videos and audio from YouTube, Instagram, and Facebook.\n🎵 <b>Music World:</b> Search music, extract audio from video, and identify tracks with Shazam.\n🗣 <b>Voice Services:</b> Convert text to speech and voice messages to text.\n🖼 <b>Image Editor:</b> Remove backgrounds and apply filters.\n🔄 <b>Professional Translator:</b> Translate text between UZ, RU, and EN.\n📢 <b>Advertising:</b> Promote your products through the bot.\n🆘 <b>Live Support:</b> Contact admins directly.\n\n🔒 <b>Security:</b> Your data is kept confidential.",
        "error": "⚠️ An error occurred.",
        "msg_wait_admin": "Your message has been sent to the admin, please wait for a reply. ⏳",
        "rate_bot": "Please rate the bot (1-5): ⭐",
        "write_feedback": "Leave your feedback and suggestions: 📝\n(You can send text, photo or video)",
        "feedback_received_return_main": "Thank you for your feedback! ✅",
        "order_deleted": "Order deleted! 🗑️",
        "chat_ended_rate": "Chat ended. 🏁\nPlease rate the service quality:",
        "support_request_sent": "Your support request has been sent. Please wait for admin response. ⏳",
        "admin_joined_chat": "✅ Admin accepted your request! 💬\nYou can chat now.",
        "admin_rejected_chat": "❌ Admin rejected your request. Try again later.",
        "chat_ended_user": "User ended the chat. ❌",
        "search_results_header": "🎵 <b>Search Results (Page {page}):</b>",
        "insta_downloading": "📥 Downloading video from Instagram...",
        "edit_profile_prompt": "Which part do you want to edit? ✏️",
        "enter_new_fullname": "Enter your new full name: 👤",
        "enter_new_region": "Select new region: 🌍",
        "enter_new_district": "Select new district: 🏘️",
        "enter_new_district_input": "Enter new district: 🏘️",
        "enter_new_neighborhood": "Select new neighborhood: 🏠",
        "enter_new_neighborhood_input": "Enter new neighborhood: 🏠",
        "enter_new_phone": "Enter your new phone number: 📞",
        "enter_new_location": "Share your new location: 📍",
        "editing_mode": "Editing mode! ✏️",
        "yt_video_found": "📹 <b>YouTube video found!</b>\nPlease select a format:",
        "choose_video_quality": "🎥 <b>Select video quality:</b>",
        "yt_downloading_res": "📥 Downloading in {resolution}p quality... Please wait.",
        "fmt_mp3": "🎵 MP3 (Audio)",
        "fmt_video": "🎬 Video (MP4)",
        "profile_updated": "Profile successfully updated! ✅",
        "btn_end_chat": "❌ End Chat",
        "confirm_delete_profile": "Do you really want to delete your profile? ⚠️",
        "yes": "✅ Yes",
        "no": "❌ No",
        "profile_deleted": "Profile deleted! 🗑️",
        "action_cancelled": "Cancelled! ❌",
        "cancelled_text": "Cancelled. ❌",
        "admin_not_admin": "You are not an admin! ❌",
        "user_is_banned": "🚫 {name}, you are banned! You cannot use the bot.",
        "bot_token_missing": "BOT_TOKEN not found! Check your .env file.",
        "bot_started": "✅ Bot started!",
        "bot_start_error": "Error starting bot: {error}",
        "bot_stopped": "Bot stopped.",
        "bot_stopped_by_admin": "Bot stopped by admin.",
        "unexpected_error": "Unexpected error: {error}",
        "already_in_chat": "You are already in a chat. 💬",
        "request_already_processed": "Request has already been processed. ⚠️",
        "chat_activated": "Chat activated! 💬\nYou can now talk to the user.\nPress the button to end 👇",
        "chat_accepted": "Chat accepted! ✅",
        "feedback_thank_you_full": "Thank you for your feedback, we appreciate it! ✅",
        "select_voice_gender": "🗣 <b>Select voice type:</b>",
        "voice_male": "👨 Male",
        "voice_female": "👩 Female",
        "profile_restored_success": "Profile successfully restored! ✅",
        "converting_to_voice": "🗣 <b>Converting to voice...</b> ⏳",
        "file_too_large_for_processing": "⚠️ Sorry, the file size exceeds the allowed limit. Please send a smaller file.",
        "send_voice_or_audio": "🗣 <b>Voice -> Text</b>\n\nSend a voice message or an audio file.",
        "music_limit_50mb_alert": "⚠️ Sorry {name}, this music size exceeds 50MB. Please download another music.",
        "profile_joined_date": "Joined date",
        "profile_days_count": "Days with bot",
        "user_unblocked_alert": "✅ {name}, you are unblocked! You can use the bot again.",
        "welcome_ads_name": "{name}, welcome to the Ads section! 📢\nHere you can promote your products or services to a wide audience through our platform. Please select the type of service 👇",
        "welcome_music_name": "{name}, welcome to the Music section! 🎵\nHere you can search for music, listen to your saved tracks, and perform other audio actions. Please select the desired button 👇",
        "welcome_video_name": "{name}, welcome to the Video section! 📹\nEasily download videos from social networks like YouTube and Instagram, or convert your own videos into a round format. Please proceed 👇",
        "welcome_image_name": "{name}, welcome to the Image section! 🖼\nEasily remove the background from your photos or apply various effects to them. Choose the desired action 👇",
        "feedback_welcome_name": "{name}, welcome to the feedback section! 💬\nLeave your feedback and suggestions: 📝",
        "btn_find_music": "🎵 Find Music (Shazam)",
        "get_audio_from_video": "🎵 Get Audio",
        "shazam_prompt": "🎵 <b>Shazam Mode</b>\n\nPlease send a short audio, voice message, or video. I will listen to it, identify the music, and download it for you! 🎧",
        "shazam_recognizing": "🎧 <b>Listening...</b> ⏳",
        "shazam_not_found": "😔 Sorry, I couldn't recognize this music.",
        "shazam_found_downloading": "🎵 <b>{title} - {artist}</b> found.\n📥 Your music is downloading, please wait. Thank you for your patience!",
        "audio_received_saved": "✅ Audio received and added to 'My Music' list.",
        "video_received_saved": "✅ Video received and added to 'My Videos' list.",
        "processed_via_bot": "🤖 Processed via @{bot_username}",
        "image_saved_alert": "Image saved! ✅",
        "no_saved_images": "😔 You have no saved images.",
        "my_images_list_header": "🖼 <b>Your Saved Images:</b>\n\n<i>Click a number to view.</i>",
        "image_deleted": "Image deleted! 🗑️",
        "page_label": "📄 Page",
        "search_btn": "🔍 Search",
        "search_music_prompt": "🎵 Enter the music name to search:",
        "search_results": "🔍 <b>Search results ({count} items):</b>",
        "phone_error": "⚠️ Please enter a valid phone number (9 digits).\nExample: 901234567",
        "share_phone": "📱 Share Phone Number",
        "session_expired": "⏳ Session expired. Please press /start.",
        "old_button": "⚠️ Button outdated. Please send /start.",
        "session_expired_alert": "Buttons expired. 🔄\nPlease send /start.",
        "enter_phone_prompt": "Send your phone number or press the button below: 📞",
        "enter_district_prompt": "Enter district name: 🏘️",
        "enter_neighborhood_prompt": "Enter neighborhood name: 🏠",
        "captcha_fail_attempts": "❌ <b>Wrong answer!</b>\n\nAttempts remaining: <b>{attempts}</b>.\n\nNew question: <b>{challenge} = ?</b>",
        "select_district_prompt": "Select district: 🏘️",
        "select_neighborhood_prompt": "Select neighborhood: 🏠",
        "profile_security_header": "Profile Security:",
        "profile_security_safe": "✅ 🔒 Your profile is in a safe state",
        "profile_security_warning": "⚠️ Profile security issue",
    }
}

# ============================================================
# Yordamchi funksiyalar
# ============================================================

def clean_path(path: str) -> str:
    """
    Windows backslash muammosini bartaraf qiladi.
    '\\' -> '/' ga almashtiradi, f-string va boshqa kutubxonalar bilan ishlash uchun xavfsiz qiladi
    """
    return str(path).replace("\\", "/")

async def safe_edit_message(callback: CallbackQuery, text: str, reply_markup=None, parse_mode="HTML"):
    """
    Xabarni xavfsiz tahrirlash uchun yordamchi funksiya.
    Agar xabar tiri o'zgargan bo'lsa (masalan, rasm -> matn), eski xabarni o'chirib yangisini yuboradi.
    """
    try:
        # Agar xabar media bo'lsa (rasm, video va h.k) va biz matn yuborayotgan bo'lsak
        if callback.message.content_type not in [ContentType.TEXT]:
            await callback.message.delete()
            await callback.message.answer(text, reply_markup=reply_markup, parse_mode=parse_mode)
        else:
            await callback.message.edit_text(text, reply_markup=reply_markup, parse_mode=parse_mode)
    except TelegramBadRequest as e:
        # Agar xabar o'zgarmagan bo'lsa yoki topilmasa
        if "message is not modified" in str(e):
            pass
        elif "message to edit not found" in str(e) or "message can't be edited" in str(e):
            # Tahrirlab bo'lmasa, yangi xabar yuboramiz
            try:
                await callback.message.delete()
            except: pass
            await callback.message.answer(text, reply_markup=reply_markup, parse_mode=parse_mode)
        else:
            logger.error(f"Safe edit error: {e}")
            # Fallback
            await callback.message.answer(text, reply_markup=reply_markup, parse_mode=parse_mode)



async def check_subscription(bot: Bot, user_id: int) -> List[str]:
    """Foydalanuvchining kanallarga obuna bo'lganligini tekshirish."""
    missing: List[str] = []
    
    # Bazadan kanallarni olish
    db_channels = await db.get_channels()
    # Agar baza bo'sh bo'lsa, .env dan olish (zaxira varianti)
    channels = [ch[1] for ch in db_channels] if db_channels else CHANNEL_LINKS

    for channel in channels:
        try:
            # Sharh: Faqat Telegram havolalarini tekshiramiz
            if channel.startswith("@") or channel.startswith("-100"):
                member = await bot.get_chat_member(chat_id=channel, user_id=user_id)
                if member.status in ("left", "kicked", "restricted"):
                    missing.append(channel)
        except Exception as e:
            logger.error("Obuna tekshiruvida xato (%s): %s", channel, e)
            missing.append(channel) # Agar kanal topilmasa yoki xato bo'lsa, obuna bo'lishni so'raymiz
    return missing

async def get_profile_evaluation(user: Optional[Tuple], lang: str = 'uz') -> str:
    """
    Foydalanuvchi profilini to'liqligini baholaydi va matnli natija qaytaradi.
    6 ta maydon tekshiriladi va 5 ballik tizimda baholanadi.
    """
    # Agar profil hali yaratilmagan bo'lsa (user[4] - full_name)
    if not user or not user[4]:
        return ""
    
    score = 0
    # Tekshiriladigan maydonlar: full_name, region, district, neighborhood, phone, location
    fields = user[4:10]
    for field in fields:
        if field:
            score += 1

    # Ballarni 5 ballik tizimga o'tkazish va statusni aniqlash
    if score == 6:
        status_key = "profile_status_excellent"
    elif score == 5:
        status_key = "profile_status_good"
    elif score in [3, 4]:
        status_key = "profile_status_satisfactory"
    elif score in [1, 2]:
        status_key = "profile_status_poor"
    else:
        status_key = "profile_status_very_poor"

    # Foydalanuvchi ismini olish (masalan, "John Doe" dan "John")
    name = user[4].split()[0]
    
    # Tarjimalardan sarlavha va status matnini olish
    header = get_text("profile_status_header", lang)
    status_text = get_text(status_key, lang, name=name)

    return f"{header}{status_text}", score

async def generate_captcha() -> Tuple[str, str]:
    """Tasodifiy CAPTCHA generatsiya qilish."""
    ops = ["+", "-", "*"]
    op = random.choice(ops)

    if op == "+":
        a, b = random.randint(1, 50), random.randint(1, 50)
    elif op == "-":
        a = random.randint(10, 100)
        b = random.randint(1, a - 1)
    else:
        a, b = random.randint(1, 12), random.randint(1, 12)

    challenge = f"{a} {op} {b}"
    answer = str(eval(challenge))  # noqa: S307 — arithmetic only
    return challenge, answer


async def get_user_profile_text(user: Optional[Tuple], lang: str = 'uz', for_admin: bool = False) -> str:
    """Foydalanuvchi profil ma'lumotlarini formatlash."""
    if not user:
        return get_text("profile_not_found", lang)

    full_name, region, district, neighborhood, phone, location = user[4:10]
    username = user[1]
    header_key = "profile_header_admin" if for_admin else "profile_header"
    
    username_line = ""
    if username:
        username_line = f"{get_text('lbl_username', lang)}: @{escape(username)}\n"

    loc_link = (
        f"<a href='https://maps.google.com/?q={location}'>{get_text('lbl_map', lang)}</a>"
        if location
        else get_text('lbl_none', lang)
    )
    profile_text = (f"<b>{get_text(header_key, lang)}</b>\n\n"
        f"🆔 ID: <code>{user[0]}</code>\n"
        f"{username_line}"
        f"{get_text('lbl_name', lang)}: {escape(full_name) if full_name else get_text('lbl_none', lang)}\n"
        f"{get_text('lbl_region', lang)}: {escape(region) if region else get_text('lbl_none', lang)}\n"
        f"{get_text('lbl_district', lang)}: {escape(district) if district else get_text('lbl_none', lang)}\n"
        f"{get_text('lbl_neighborhood', lang)}: {escape(neighborhood) if neighborhood else get_text('lbl_none', lang)}\n"
        f"{get_text('lbl_phone', lang)}: {escape(phone) if phone else get_text('lbl_none', lang)}\n"
        f"{get_text('lbl_address', lang)}: {loc_link}")

    # Sharh: Botga qo'shilgan vaqt va kunlar sonini hisoblash
    joined_at_iso = user[11]
    days_with_bot = 0
    joined_date_str = "Noma'lum"
    if joined_at_iso:
        try:
            joined_dt = datetime.fromisoformat(joined_at_iso)
            days_with_bot = (datetime.now() - joined_dt).days
            joined_date_str = joined_dt.strftime("%d.%m.%Y")
        except: pass
    
    stats_text = f"\n📅 {get_text('profile_joined_date', lang)}: {joined_date_str}\n" \
                 f"⏳ {get_text('profile_days_count', lang)}: {days_with_bot} kun\n"

    daily_stats_count = await db.get_user_daily_stats(user[0])
    daily_stats_text = get_text("profile_daily_stats", lang, count=daily_stats_count)

    evaluation_text, score = await get_profile_evaluation(user, lang)

    security_status_key = "profile_security_safe" if score == 6 else "profile_security_warning"
    security_text = f"\n{get_text('profile_security_header', lang)} {get_text(security_status_key, lang)}"

    return profile_text + stats_text + daily_stats_text + evaluation_text + security_text

def make_progress_bar(value: int, total: int, length: int = 10) -> str:
    """Statistika uchun progress bar yaratish"""
    if total == 0:
        return "░" * length
    filled_length = int(length * value // total)
    return "█" * filled_length + "░" * (length - filled_length)

# Tarjima kesh (Google rate-limit oldini olish)
_TRANSLATION_CACHE: Dict[str, str] = {}

def _translate_sync(source_lang: str, target_lang: str, text_to_translate: str) -> str:
    """Tarjimani bloklamaydigan sinxron worker.
    Avval deep-translator, keyin Google Translate endpoint ishlatiladi.
    """
    source_lang = (source_lang or "").lower().strip()
    target_lang = (target_lang or "").lower().strip()
    text_to_translate = (text_to_translate or "").strip()

    if source_lang not in {"uz", "ru", "en"} or target_lang not in {"uz", "ru", "en"}:
        raise ValueError("Qo'llab-quvvatlanmaydigan til")
    if not text_to_translate:
        raise ValueError("Tarjima uchun matn bo'sh")
    if source_lang == target_lang:
        return text_to_translate

    if GOOGLE_TRANSLATOR_AVAILABLE and GoogleTranslator is not None:
        try:
            result = GoogleTranslator(source=source_lang, target=target_lang).translate(text_to_translate)
            if result and result.strip():
                return result.strip()
        except Exception as exc:
            logger.warning("deep-translator ishlamadi, fallback ishlatiladi: %s", exc)

    query = urllib.parse.urlencode({
        "client": "gtx",
        "sl": source_lang,
        "tl": target_lang,
        "dt": "t",
        "q": text_to_translate,
    })
    url = "https://translate.googleapis.com/translate_a/single?" + query
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "Mozilla/5.0"},
    )
    with urllib.request.urlopen(request, timeout=20) as response:
        payload = json.loads(response.read().decode("utf-8"))
    parts = payload[0] if isinstance(payload, list) and payload else []
    translated = "".join(
        part[0] for part in parts
        if isinstance(part, list) and part and isinstance(part[0], str)
    ).strip()
    if not translated:
        raise RuntimeError("Tarjima serveridan bo'sh javob qaytdi")
    return translated


def get_text(key: str, lang: str = 'uz', **kwargs) -> str:
    """
    Tarjima matnini olish.
    1. TRANSLATIONS lug'atidan qidiradi.
    2. Topilmasa — o'zbekcha fallback (Google avtomatik chaqirilMAYDI — rate-limit oldini olish).
    3. Faqat aniq tarjima bo'limida Google ishlatiladi.
    """
    try:
        lang = (lang or 'uz').lower()
        if lang not in ('uz', 'ru', 'en'):
            lang = 'uz'

        lang_dict = TRANSLATIONS.get(lang) or TRANSLATIONS.get('uz', {})
        uz_dict = TRANSLATIONS.get('uz', {})

        text = lang_dict.get(key)
        if text is None:
            # RU/EN da yo'q bo'lsa o'zbekchadan olamiz (HTML/ikonka buzilmasin)
            text = uz_dict.get(key, key)

        try:
            return text.format(**kwargs) if kwargs else text
        except (KeyError, ValueError):
            return text

    except Exception as e:
        logger.warning(f"⚠️ [TARJIMA XATOLIK]: {e}")
        try:
            return key.format(**kwargs) if kwargs else key
        except Exception:
            return str(key)
        
async def get_user_lang(user_id: int) -> str:
    return await db.get_user_language(user_id)

async def notify_admins(bot: Bot, message_text: str):
    """Adminlarga muhim ogohlantirish yuborish"""
    for admin_id in ADMIN_IDS:
        try:
            # Admin tilini olish (agar kerak bo'lsa, hozircha faqat 'uz' da yuboriladi)
            # Hozircha, ogohlantirishlar uchun 'uz' default qilib qoldiramiz.
            await bot.send_message(admin_id, message_text, parse_mode="HTML")
        except Exception as e:
            logger.error(f"Adminga xabar yuborishda xato ({admin_id}): {e}")

def progress_hook(d, bot: Bot, message: Message, last_update_time, loop, lang: str = 'uz', finished_text_key: str = "music_almost_ready"):
    status = d.get('status')
    current_time = time.time()

    if status in ('downloading', 'extracting', 'merging'):
        if current_time - last_update_time[0] > 1:
            try:
                ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
                percentage = d.get('_percent_str') or ''
                percentage = ansi_escape.sub('', percentage).strip()

                downloaded = d.get('downloaded_bytes') or d.get('downloaded_bytes_approx') or 0
                total = d.get('total_bytes') or d.get('total_bytes_estimate') or 0
                downloaded_mb = downloaded / (1024 * 1024)
                total_mb = total / (1024 * 1024) if total else 0

                if not percentage:
                    percentage = f"{(downloaded_mb / total_mb * 100) if total_mb else 0:.2f}%"

                progress_text = f"📥 <b>Yuklanmoqda...</b> {percentage}"
                if total_mb:
                    progress_text += f"\n({downloaded_mb:.2f} MB / {total_mb:.2f} MB)"
                elif downloaded_mb:
                    progress_text += f"\n({downloaded_mb:.2f} MB)"

                asyncio.run_coroutine_threadsafe(
                    bot.edit_message_text(
                        progress_text,
                        chat_id=message.chat.id,
                        message_id=message.message_id,
                        parse_mode="HTML"
                    ),
                    loop
                )
                last_update_time[0] = current_time
            except Exception:
                pass
    elif status == 'finished':
        try:
            asyncio.run_coroutine_threadsafe(
                bot.edit_message_text(
                    get_text(finished_text_key, lang),
                    chat_id=message.chat.id,
                    message_id=message.message_id,
                    parse_mode="HTML"
                ),
                loop
            )
        except Exception:
            pass

async def safe_remove(path: str, retries: int = 5, delay: float = 1.0):
    """Faylni xavfsiz o'chirish (Windows WinError 32 oldini olish uchun)"""
    clean_p = clean_path(path)
    for i in range(retries):
        try:
            if os.path.exists(clean_p):
                os.remove(clean_p)
            return
        except PermissionError:
            if i < retries - 1:
                await asyncio.sleep(delay)
        except Exception as e:
            logger.error(f"Faylni o'chirishda xato {clean_p}: {e}")
            return

async def finish_profile_edit(message_or_callback: Union[Message, CallbackQuery], state: FSMContext):
    """Profil tahrirlashni yakunlash uchun yordamchi funksiya."""
    await clear_state_preserve_session(state)
    
    user_id = message_or_callback.from_user.id
    lang = await get_user_lang(user_id)
    user = await db.get_user(user_id)
    profile_text = await get_user_profile_text(user, lang)
    
    if isinstance(message_or_callback, CallbackQuery):
        msg_obj = message_or_callback.message
        await msg_obj.delete()
        await message_or_callback.answer()
    else:
        msg_obj = message_or_callback

    await msg_obj.answer(get_text("profile_updated", lang))
    
    # Profilni qayta ko'rsatish (profile_handler logikasi kabi)
    photo_id = user[18] if user and len(user) > 18 and user[18] else None
    # Rasm bilan yoki rasmsiz yuborish
    await send_profile_view(msg_obj, user_id, profile_text, photo_id, True, lang)
    

# ------------------------------------------------------------
# Userbot orqali yuklash uchun progress funksiyasi (foydalanuvchi so'rovi)
# ------------------------------------------------------------
async def upload_progress_hook(current, total, bot: Bot, message: Message, last_update_time):
    """Userbot orqali fayl yuklanish jarayonini ko'rsatib turuvchi funksiya."""
    current_time = time.time()
    # Xabarni har 2 soniyada yangilab turish (Telegram limitlariga tushmaslik uchun)
    if current_time - last_update_time[0] > 2:
        try:
            percentage = (current / total) * 100
            # Yuklanish foizini va hajmini ko'rsatish
            await bot.edit_message_text(
                f"📦 Kanalga yuklanmoqda: {percentage:.2f}%\n"
                f"({current/1024/1024:.2f} MB / {total/1024/1024:.2f} MB)",
                chat_id=message.chat.id,
                message_id=message.message_id
            )
            last_update_time[0] = current_time
        except Exception:
            pass # Xabar o'zgarmagan bo'lsa yoki boshqa xato bo'lsa, jim o'tish

async def is_user_admin(user_id: int) -> bool:
    """Foydalanuvchi admin ekanligini tekshirish (env yoki db)"""
    return user_id in ADMIN_IDS or await db.is_user_admin(user_id)


# ============================================================
# Klaviatura quriluvchilari
# ============================================================
def main_menu_keyboard(is_admin: bool = False, lang: str = 'uz', user_name: Optional[str] = None):
    builder = InlineKeyboardBuilder()
    
    builder.add(InlineKeyboardButton(text=get_text("ads", lang), callback_data="menu_ads"))
    builder.add(InlineKeyboardButton(text=get_text("music", lang), callback_data="menu_music"))
    builder.add(InlineKeyboardButton(text=get_text("video_section", lang), callback_data="menu_video"))
    builder.add(InlineKeyboardButton(text=get_text("image_section", lang), callback_data="menu_image"))
    builder.add(InlineKeyboardButton(text=get_text("support", lang), callback_data="menu_support"))
    builder.add(InlineKeyboardButton(text=get_text("feedback", lang), callback_data="menu_feedback"))
    builder.add(InlineKeyboardButton(text=get_text("about", lang), callback_data="menu_about"))
    builder.add(InlineKeyboardButton(text=get_text("translate", lang), callback_data="menu_translate")) # Hamma uchun profil tepasida
    builder.add(InlineKeyboardButton(text=get_text("profile", lang), callback_data="menu_profile"))
    builder.add(InlineKeyboardButton(text=get_text("settings", lang), callback_data="menu_settings"))
    if is_admin:
        builder.add(InlineKeyboardButton(text=get_text("admin", lang), callback_data="admin_panel"))
    builder.adjust(1)
    return builder.as_markup()

def music_menu_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("my_music", lang), callback_data="menu_my_music"))
    builder.add(InlineKeyboardButton(text=get_text("voice_to_text_btn", lang), callback_data="voice_to_text"))
    builder.add(InlineKeyboardButton(text=get_text("video_to_mp3_btn", lang), callback_data="video_to_mp3"))
    builder.add(InlineKeyboardButton(text=get_text("shazam_btn", lang), callback_data="music_shazam"))
    builder.add(InlineKeyboardButton(text=get_text("music_search_btn", lang), callback_data="music_start_search"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def image_menu_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("my_images", lang), callback_data="menu_my_images"))
    builder.add(InlineKeyboardButton(text=get_text("btn_remove_bg", lang), callback_data="img_rm_bg"))
    builder.add(InlineKeyboardButton(text=get_text("btn_filter", lang), callback_data="img_filter"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1) # Vertikal
    return builder.as_markup()

def support_waiting_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("cancel", lang), callback_data="support_cancel"))
    builder.adjust(1)
    return builder.as_markup()

def support_active_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("btn_end_chat", lang), callback_data="support_end"))
    # Bosh menyuga tugmasi kerak emas, chunki chat aktiv paytda faqat tugatish kerak
    builder.adjust(1)
    return builder.as_markup()

def admin_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="📂 Ma'lumotlar", callback_data="admin_data"))
    builder.add(InlineKeyboardButton(text="📢 Elon yuborish", callback_data="admin_broadcast"))
    builder.add(InlineKeyboardButton(text="🛒 Buyurtmalar", callback_data="admin_orders"))
    builder.add(InlineKeyboardButton(text="📢 Kanallar", callback_data="admin_channels"))
    builder.add(InlineKeyboardButton(text="📹 Video qo'llanma", callback_data="admin_video_guide"))
    builder.add(InlineKeyboardButton(text="🔍 Foydalanuvchi qidirish", callback_data="admin_search_user"))
    builder.add(InlineKeyboardButton(text="🏠 Bosh menyuga", callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def data_menu_keyboard(lang: str = 'uz'):
    # Foydalanuvchi talabiga binoan, ma'lumotlar bilan bog'liq menyular bir joyga yig'ildi.
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="📊 Statistika", callback_data="admin_stats"))
    builder.add(InlineKeyboardButton(text="👥 Foydalanuvchilar", callback_data="admin_users"))
    builder.add(InlineKeyboardButton(text="🚫 Bloklanganlar", callback_data="admin_banned"))
    builder.add(InlineKeyboardButton(text="⬅️ Admin panelga", callback_data="admin_panel"))
    builder.adjust(1)
    return builder.as_markup()

def regions_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    for region in REGIONS:
        builder.add(InlineKeyboardButton(text=region, callback_data=f"region_{region}"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(2)
    return builder.as_markup()

def districts_keyboard(region: str, lang: str = 'uz'):
    if region not in DISTRICTS:
        return None
    builder = InlineKeyboardBuilder()
    for district in DISTRICTS[region]:
        builder.add(InlineKeyboardButton(text=district, callback_data=f"district_{district}"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(2)
    return builder.as_markup()

def neighborhoods_keyboard(district: str, lang: str = 'uz'):
    if district not in NEIGHBORHOODS:
        return None
    builder = InlineKeyboardBuilder()
    for neigh in NEIGHBORHOODS[district]: # noqa
        builder.add(InlineKeyboardButton(text=neigh, callback_data=f"neigh_{neigh}")) # noqa
    # Har bir qatorda 3 ta tugma bo'lishini ta'minlash
    builder.adjust(3)
    # Bosh menyuga qaytish tugmasini yangi qatorga qo'shish
    builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    return builder.as_markup()

async def profile_keyboard(has_profile: bool = False, lang: str = 'uz', user_id: int = None):
    builder = InlineKeyboardBuilder()
    if has_profile:
        builder.add(InlineKeyboardButton(text=get_text("btn_edit_profile", lang), callback_data="edit_profile"))
        builder.add(InlineKeyboardButton(text=get_text("btn_delete_profile", lang), callback_data="delete_profile")) # noqa
    else:
        builder.add(InlineKeyboardButton(text=get_text("btn_create_profile", lang), callback_data="create_profile"))
        if user_id and await db.has_deleted_profile(user_id):
            builder.add(InlineKeyboardButton(text=get_text("btn_restore_profile", lang), callback_data="restore_profile"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def edit_profile_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("lbl_name", lang), callback_data="edit_full_name"))
    builder.add(InlineKeyboardButton(text=get_text("lbl_region", lang), callback_data="edit_region"))
    builder.add(InlineKeyboardButton(text=get_text("lbl_district", lang), callback_data="edit_district"))
    builder.add(InlineKeyboardButton(text=get_text("lbl_neighborhood", lang), callback_data="edit_neighborhood"))
    builder.add(InlineKeyboardButton(text=get_text("lbl_phone", lang), callback_data="edit_phone"))
    builder.add(InlineKeyboardButton(text=get_text("lbl_address", lang), callback_data="edit_location"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(2)
    return builder.as_markup()

def confirm_delete_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", lang), callback_data="confirm_delete_yes"))
    builder.add(InlineKeyboardButton(text=get_text("no", lang), callback_data="confirm_delete_no"))
    builder.adjust(2)
    return builder.as_markup()

def confirm_unblock_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", lang), callback_data="confirm_unblock_yes"))
    builder.add(InlineKeyboardButton(text=get_text("no", lang), callback_data="confirm_unblock_no"))
    builder.adjust(2)
    return builder.as_markup()

def cancel_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    return builder.as_markup()

def back_to_main_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    return builder.as_markup()

def phone_keyboard(lang: str = 'uz'):
    builder = ReplyKeyboardBuilder()
    builder.add(KeyboardButton(text=get_text("share_phone", lang), request_contact=True))
    return builder.as_markup(resize_keyboard=True, one_time_keyboard=True)

def back_to_admin_keyboard():
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="⬅️ Admin panelga qaytish", callback_data="admin_panel"))
    return builder.as_markup()

def location_keyboard(lang: str = 'uz'):
    builder = ReplyKeyboardBuilder()
    builder.add(KeyboardButton(text=get_text("share_location", lang), request_location=True))
    # Sharh: one_time_keyboard=True qo'shildi. Bu tugma bosilgandan so'ng klaviatura avtomatik yashirinadi.
    return builder.as_markup(resize_keyboard=True, one_time_keyboard=True)

def like_keyboard():
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="✅ Ha", callback_data="like_yes"))
    builder.add(InlineKeyboardButton(text="❌ Yo'q", callback_data="like_no"))
    builder.adjust(2)
    return builder.as_markup()

def rating_keyboard():
    builder = InlineKeyboardBuilder()
    for i in range(1, 6):
        builder.add(InlineKeyboardButton(text=f"{i}", callback_data=f"rating_{i}"))
    builder.adjust(5)
    return builder.as_markup()

def order_actions_keyboard(order_id: int, lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("btn_completed", lang), callback_data=f"order_complete_{order_id}"))
    builder.add(InlineKeyboardButton(text=get_text("btn_later", lang), callback_data=f"order_later_{order_id}"))
    builder.add(InlineKeyboardButton(text="❌ Bekor qilish", callback_data=f"order_cancel_{order_id}"))
    builder.adjust(1)
    return builder.as_markup()

def blocked_user_keyboard(lang: str = 'uz'):
    """Bloklangan foydalanuvchi uchun klaviatura (faqat shikoyat)"""
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="✍️ Shikoyat yuborish", callback_data="send_complaint"))
    return builder.as_markup()




def support_accept_keyboard(user_id: int):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="✅ Qabul qilish", callback_data=f"accept_support_{user_id}"))
    builder.add(InlineKeyboardButton(text="❌ Rad etish", callback_data=f"reject_support_{user_id}"))
    builder.adjust(2)
    return builder.as_markup()

def admin_user_actions_keyboard(user_id: int, is_banned: bool = False, is_admin: bool = False, is_special: bool = False, lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    
    # Bloklash/Ochish
    block_text = get_text("admin_action_unblock", lang) if is_banned else get_text("admin_action_block", lang)
    block_action = f"admin_unblock_{user_id}" if is_banned else f"admin_block_{user_id}"
    builder.add(InlineKeyboardButton(text=block_text, callback_data=block_action))
    
    # Admin qilish/olish
    admin_text = get_text("admin_revoke_admin", lang) if is_admin else get_text("admin_grant_admin", lang)
    admin_action = f"perm_admin_0_{user_id}" if is_admin else f"perm_admin_1_{user_id}"
    builder.add(InlineKeyboardButton(text=admin_text, callback_data=admin_action))

    # Maxsus ruxsat
    special_text = get_text("admin_revoke_special", lang) if is_special else get_text("admin_grant_special", lang)
    special_action = f"perm_special_0_{user_id}" if is_special else f"perm_special_1_{user_id}"
    builder.add(InlineKeyboardButton(text=special_text, callback_data=special_action))

    builder.add(InlineKeyboardButton(text=get_text("admin_action_notify", lang), callback_data=f"admin_notify_{user_id}"))
    builder.add(InlineKeyboardButton(text="❌ Bekor qilish", callback_data="admin_cancel_action"))
    builder.adjust(1)
    return builder.as_markup()

def settings_language_keyboard(lang: str = 'uz', selected_lang: str = None):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("lang_uz", lang), callback_data="set_lang_uz"))
    builder.add(InlineKeyboardButton(text=get_text("lang_ru", lang), callback_data="set_lang_ru"))
    builder.add(InlineKeyboardButton(text=get_text("lang_en", lang), callback_data="set_lang_en"))
    
    if selected_lang:
        builder.add(InlineKeyboardButton(text=get_text("save", selected_lang), callback_data=f"save_lang_{selected_lang}"))
        
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def music_results_keyboard(results_on_page, page, total_pages, total_items, lang='uz'):
    """Musiqa natijalari uchun klaviatura (10 ta tugma)"""
    builder = InlineKeyboardBuilder()
    
    # 10 ta tugmani 2 qatorga joylash (5 tadan)
    row1 = []
    row2 = []
    for i, result in enumerate(results_on_page):
        actual_index = page * 10 + i
        btn = InlineKeyboardButton(text=f"🎵 {i+1}", callback_data=f"dl_music_{result['id']}")
        if i < 5:
            row1.append(btn)
        else:
            row2.append(btn)
    
    if row1: builder.row(*row1)
    if row2: builder.row(*row2)
    
    # Sahifalash tugmalari (Oldinga / Orqaga)
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton(text=get_text("btn_prev_page", lang), callback_data=f"music_page_{page-1}"))
    
    # Sahifa raqami
    nav_row.append(InlineKeyboardButton(text=f"📄 {page+1}/{total_pages}", callback_data="noop"))

    if (page + 1) < total_pages:
        nav_row.append(InlineKeyboardButton(text=get_text("btn_next_page", lang), callback_data=f"music_page_{page+1}"))
    
    builder.row(*nav_row)
    builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    
    return builder.as_markup()

def video_actions_keyboard(lang: str = 'uz', video_id: str = None, is_youtube: bool = False, is_shorts: bool = False):
    """Video ostida chiqadigan universal tugmalar (Yangilangan)"""
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("save_video", lang), callback_data="save_current_video"))
    
    # Agar YouTube gorizontal video bo'lsa -> Musiqasini olish (Audio ekstraksiya)
    if is_youtube and not is_shorts and video_id:
        builder.add(InlineKeyboardButton(text=get_text("get_audio_from_video", lang), callback_data=f"yt_audio_from_video_{video_id}"))
    # Agar Shorts, Instagram, Facebook bo'lsa -> Musiqasini topish (Shazam)
    else:
        if is_youtube and video_id:
             # YouTube Shorts uchun ID orqali Shazam
             builder.add(InlineKeyboardButton(text=get_text("btn_find_music", lang), callback_data=f"yt_shazam_full_{video_id}"))
        else:
             # Boshqa videolar (Insta, FB) uchun xabardagi media orqali Shazam
             builder.add(InlineKeyboardButton(text=get_text("btn_find_music", lang), callback_data="find_music_from_msg"))

    builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def youtube_format_keyboard(video_id, lang='uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("fmt_mp3", lang), callback_data=f"yt_fmt_mp3_{video_id}"))
    builder.add(InlineKeyboardButton(text=get_text("fmt_video", lang), callback_data=f"yt_fmt_video_{video_id}"))
    builder.add(InlineKeyboardButton(text=get_text("cancel", lang), callback_data="cancel"))
    builder.adjust(2, 1)
    return builder.as_markup()

def youtube_resolution_keyboard(video_id, lang='uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text="🎥 1080p", callback_data=f"yt_dl_res_{video_id}_1080"))
    builder.add(InlineKeyboardButton(text="🎥 720p", callback_data=f"yt_dl_res_{video_id}_720"))
    builder.add(InlineKeyboardButton(text="🎥 480p", callback_data=f"yt_dl_res_{video_id}_480"))
    builder.add(InlineKeyboardButton(text=get_text("cancel", lang), callback_data="cancel"))
    builder.adjust(1)
    return builder.as_markup()

def instagram_post_actions_keyboard(shortcode: str, lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("save_video", lang), callback_data="save_current_video"))
    # Musiqasini topish (Shazam) - universal handler orqali
    builder.add(InlineKeyboardButton(text=get_text("btn_find_music", lang), callback_data="find_music_from_msg"))
    builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()


# Reklama uchun klaviaturalar
def ads_type_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("ads_social", lang), callback_data="ads_type_social"))
    builder.add(InlineKeyboardButton(text=get_text("ads_simple_text", lang), callback_data="ads_type_simple"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def ads_platform_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("ads_platform_insta", lang), callback_data="ads_plat_instagram"))
    builder.add(InlineKeyboardButton(text=get_text("ads_platform_tg", lang), callback_data="ads_plat_telegram"))
    builder.add(InlineKeyboardButton(text=get_text("ads_platform_all", lang), callback_data="ads_plat_all"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    return builder.as_markup()

def ads_media_ask_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", lang), callback_data="ads_media_yes"))
    builder.add(InlineKeyboardButton(text=get_text("no", lang), callback_data="ads_media_no"))
    builder.adjust(2)
    return builder.as_markup()

def ads_confirm_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("ads_btn_confirm", lang), callback_data="ads_action_confirm"))
    builder.add(InlineKeyboardButton(text=get_text("ads_btn_edit", lang), callback_data="ads_action_edit"))
    builder.add(InlineKeyboardButton(text=get_text("ads_btn_cancel", lang), callback_data="ads_action_cancel"))
    builder.adjust(1)
    return builder.as_markup()

def ads_edit_select_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("ads_edit_platform", lang), callback_data="ads_edit_platform"))
    builder.add(InlineKeyboardButton(text=get_text("ads_edit_media", lang), callback_data="ads_edit_media"))
    builder.add(InlineKeyboardButton(text=get_text("ads_edit_text", lang), callback_data="ads_edit_text"))
    builder.add(InlineKeyboardButton(text=get_text("ads_btn_cancel", lang), callback_data="ads_action_cancel"))
    builder.adjust(1)
    return builder.as_markup()

def ads_save_changes_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("save", lang), callback_data="ads_save_yes"))
    builder.add(InlineKeyboardButton(text=get_text("cancel", lang), callback_data="ads_save_no"))
    builder.adjust(2)
    return builder.as_markup()

async def send_unblock_notification(bot: Bot, user_id: int):
    """Foydalanuvchi blokdan chiqqanda xabar berish"""
    # Blok vaqtini olish
    expire_time = TEMP_BLOCKS.get(user_id, 0)
    wait_time = expire_time - time.time()
    
    if wait_time > 0:
        await asyncio.sleep(wait_time)
    
    if user_id in TEMP_BLOCKS:
        del TEMP_BLOCKS[user_id]
    
    try:
        await bot.send_message(user_id, "✅ <b>Bloklash muddati tugadi!</b>\nSiz yana botdan foydalanishingiz mumkin.", parse_mode="HTML")
    except Exception as e:
        logger.error(f"Unblock notification error: {e}")

async def clear_state_preserve_session(state: FSMContext):
    """State'ni tozalaydi, lekin session_start vaqtini saqlab qoladi."""
    data = await state.get_data()
    session_start = data.get('session_start')
    await state.clear()
    if session_start:
        await state.update_data(session_start=session_start)

async def unblock_and_show_menu(bot: Bot, user_id: int):
    """
    Vaqtinchalik blok muddati tugashini kutadi, foydalanuvchini blokdan chiqaradi va bosh menyuni ko'rsatadi.
    """
    # Fetch user data from DB to get temp_block_until
    user = await db.get_user(user_id)
    if user and len(user) > 21 and user[21]: # temp_block_until is at index 21
        expire_time_str = user[21]
        expire_time = datetime.fromisoformat(expire_time_str).timestamp()
        wait_time = expire_time - time.time()
        
        if wait_time > 0:
            await asyncio.sleep(wait_time)
        
        # Clear temp_block_until in DB
        await db.update_user_field(user_id, "temp_block_until", None)
        
        try:
            lang = await get_user_lang(user_id)
            await bot.send_message(user_id, "✅ Bloklash muddati tugadi! Botdan qayta foydalanishingiz mumkin.", parse_mode="HTML")
            
            # Bosh menyuni ko'rsatish
            is_admin = await is_user_admin(user_id)
            user = await db.get_user(user_id) # Re-fetch user after unblock
            has_profile = await db.has_profile(user_id)
            display_name = user[4] if (has_profile and user and user[4]) else user[2] # user[2] is first_name
            
            await bot.send_message(
                user_id,
                get_text("welcome_ready", lang, name=escape(display_name, quote=False)),
                reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name),
            )
        except Exception as e:
            logger.error(f"Foydalanuvchini blokdan chiqarish va menyu ko'rsatishda xato ({user_id}): {e}")
    else:
        logger.info(f"User {user_id} was not temp blocked or block expired already.")

# ============================================================
# Middleware — Obuna tekshiruvi
# ============================================================
class SubscriptionMiddleware:
    def __init__(self, bot: Bot):
        self.bot = bot

    async def __call__(
        self,
        handler: Callable[[Union[Message, CallbackQuery], Dict[str, Any]], Awaitable[Any]],
        event: Union[Message, CallbackQuery],
        data: Dict[str, Any],
    ) -> Any:
        if event.from_user is None:
            return await handler(event, data)

        user_id = event.from_user.id

        if user_id is None:
             return await handler(event, data)

        await db.add_user(
            user_id,
            event.from_user.username,
            event.from_user.first_name,
            event.from_user.last_name
        )

        if await db.is_special_user(user_id):
            return await handler(event, data)

        if await is_user_admin(user_id): 
            return await handler(event, data)

        lang = await get_user_lang(user_id) # Tilni oldindan olish

        # Check for temporary block from DB
        user_db = await db.get_user(user_id)
        if user_db and len(user_db) > 21 and user_db[21]: # temp_block_until is at index 21
            expire_time_str = user_db[21]
            expire_time = datetime.fromisoformat(expire_time_str).timestamp()
            if time.time() < expire_time:
                wait_time = int((expire_time - time.time()) / 60) + 1
                msg = get_text("temp_blocked", lang, wait_time=wait_time, name=event.from_user.first_name) # noqa
                if isinstance(event, CallbackQuery): # noqa
                    await event.answer(msg, show_alert=True) # noqa
                elif isinstance(event, Message): # noqa
                    await event.answer(msg, parse_mode="HTML") # noqa
                return
            else: # Block expired, clear it from DB
                await db.update_user_field(user_id, "temp_block_until", None)

        # 24 soatlik tugma vaqti tekshiruvi (Yangi funksiya)
        if isinstance(event, CallbackQuery) and event.message and event.message.date:
            msg_date = event.message.date
            # Vaqt zonasini to'g'irlash (Telegram UTC da beradi)
            if msg_date.tzinfo is None:
                msg_date = msg_date.replace(tzinfo=timezone.utc)
            now = datetime.now(timezone.utc)
            
            if (now - msg_date) > timedelta(hours=24):
                await event.answer("⚠️ Bu tugmalar eskirgan (24 soatdan oshgan).\nIltimos, /start buyrug‘ini qayta yuboring.", show_alert=True)
                return

        # Obuna tekshiruvi
        if isinstance(event, Message) and event.text and event.text.startswith("/start"):
            pass # Start handleri o'zi tekshiradi
        else:
            missing = await check_subscription(self.bot, user_id)
            if missing:
                builder = InlineKeyboardBuilder()
                for ch in missing:
                    channel_name = ch.replace("@", "")
                    builder.add(
                        InlineKeyboardButton(text=f"📢 {channel_name}", url=f"https://t.me/{channel_name}")
                    )
                builder.add(InlineKeyboardButton(text="✅ Obuna bo'ldim", callback_data=f"check_sub_{user_id}")) # User ID bilan bog'landi
                builder.adjust(1)

                if isinstance(event, CallbackQuery):
                    await event.answer("Siz hali barcha kanallarga obuna bo'lmagansiz!", show_alert=True)
                    try: await event.message.edit_reply_markup(reply_markup=builder.as_markup())
                    except: pass
                else:
                    await event.reply("Iltimos, quyidagi kanallarga obuna bo'ling va tasdiqlang 👇", reply_markup=builder.as_markup())
                return  # handlerga o'tkazmaymiz

        # Profil tekshiruvi
        allowed_commands = ["/start"]

        # Profilsiz kirish mumkin bo'lgan callbacklar (Musiqa, Bot haqida va yangi funksiyalar)
        allowed_callbacks = [
            "create_profile", "check_sub", "restore_profile",
            "menu_music", "menu_about", "music_start_search", "menu_my_music", "menu_my_videos", "my_music_search_start",
            "menu_main", "voice_to_text", "video_to_mp3", "menu_video", "menu_image", "save_current_video", "save_current_music",
            "menu_settings", "set_lang_uz", "set_lang_ru", "set_lang_en", "video_mode_round", "video_mode_link",
            "delete_all_videos_ask", "confirm_delete_videos_yes", "confirm_delete_videos_no", "restore_all_videos", "menu_feedback"
        ]
        
        is_creating_profile = False
        if isinstance(event, Message):
            if event.text and any(event.text.startswith(cmd) for cmd in allowed_commands):
                is_creating_profile = True
        elif isinstance(event, CallbackQuery):
            if (event.data in allowed_callbacks or
                any(event.data.startswith(p) for p in ["region_", "district_", "neigh_", "music_", "yt_", "dl_", "play_", "my_music_", "my_videos_", "insta_", "save_current_music", "del_music_btn_", "del_video_btn_", "save_lang_"])):
                is_creating_profile = True

        if not await db.has_profile(user_id) and not is_creating_profile:
            fsm_state = data.get('state')
            current_state = await fsm_state.get_state() if fsm_state else None # noqa

            allowed_states = [
                UserStates.music_search.state, UserStates.my_music.state, UserStates.my_videos.state, UserStates.video_to_mp3.state, UserStates.voice_to_text.state,
                UserStates.video_download.state, UserStates.round_video.state, UserStates.settings.state, UserStates.image_menu.state, UserStates.my_images.state,
                UserStates.image_rm_bg.state, UserStates.image_filter.state, UserStates.feedback.state, UserStates.my_music_search.state,
                UserStates.support_chat.state, UserStates.complaint.state, UserStates.edit_music.state,
                UserStates.edit_full_name.state, UserStates.edit_region.state, UserStates.edit_district.state,
                UserStates.edit_neighborhood.state, UserStates.edit_phone.state, UserStates.edit_location.state, 
                UserStates.confirm_delete.state, UserStates.edit_video_caption.state, UserStates.edit_image_caption.state
            ] # noqa

            profile_states = [
                UserStates.full_name.state, UserStates.region.state, UserStates.district.state, # noqa
                UserStates.neighborhood.state, UserStates.phone.state, UserStates.location.state,
                UserStates.captcha.state
            ]

            if current_state not in profile_states and current_state not in allowed_states and not is_creating_profile:
                lang = await get_user_lang(user_id) # noqa
                if isinstance(event, CallbackQuery):
                    await event.message.edit_text("Botdan foydalanish uchun profil yaratishingiz shart! 👤", reply_markup=await profile_keyboard(has_profile=False, lang=lang, user_id=user_id))
                    await event.answer()
                else:
                    await event.answer("Botdan foydalanish uchun profil yaratishingiz shart! 👤", reply_markup=await profile_keyboard(has_profile=False, lang=lang, user_id=user_id))
                return

        user = await db.get_user(user_id)
        if user and user[10] == 1:  # is_banned
            if len(user) > 19 and user[19] == 1:
                msg = "Siz yaqinda shikoyat yubordingiz. Iltimos, adminlar ko'rib chiqishini kuting."
                if isinstance(event, CallbackQuery):
                    await event.answer(msg, show_alert=True)
                elif isinstance(event, Message):
                    await event.answer(msg)
                return

            fsm_state = data.get('state')
            current_state = await fsm_state.get_state() if fsm_state else None

            is_complaint_action = (
                (isinstance(event, CallbackQuery) and event.data == "send_complaint") or
                (isinstance(event, Message) and current_state == UserStates.complaint)
            )

            if is_complaint_action:
                return await handler(event, data)

            lang = await get_user_lang(user_id)
            kb = blocked_user_keyboard(lang) # Shikoyat yuborish tugmasi
            msg = get_text("user_is_banned", lang, name=event.from_user.first_name)

            if isinstance(event, Message):
                await event.answer(msg, reply_markup=kb)
            elif isinstance(event, CallbackQuery):
                await event.answer(get_text("user_is_banned_alert", lang, name=event.from_user.first_name), show_alert=True)
            return  # Boshqa handlerlarga o'tkazmaymiz

        # CAPTCHA tekshiruvi
        if await db.needs_captcha(user_id):
            if isinstance(event, Message) and event.text and event.text.startswith("/start"):
                pass
            elif isinstance(event, CallbackQuery):
                # FIX: Obunani tekshirish tugmasiga ruxsat berish
                if event.data == "check_sub":
                    return await handler(event, data)
                await event.answer("⚠️ Iltimos, avval xavfsizlik misolini yeching!", show_alert=True)
                return
            
            else:
                fsm_state = data.get('state')
                current_state = await fsm_state.get_state() if fsm_state else None
                
                if current_state != UserStates.captcha:
                    challenge, answer = await generate_captcha()
                    await db.set_captcha(user_id, challenge, answer)
                    await fsm_state.set_state(UserStates.captcha)
                    await event.answer(f"🛡 <b>Xavfsizlik tekshiruvi!</b>\n\nBotdan foydalanish uchun misolni yeching:\n\n<b>{challenge} = ?</b>", parse_mode="HTML")
                    return # Handlerga o'tkazmaymiz

        await db.update_user_field(user_id, "last_active", datetime.now().isoformat())
        
        return await handler(event, data)

# ============================================================
# /start komanda
# ============================================================
# Sharh: Command("start") ishlatildi, chunki CommandStart() ba'zan guruhlarda /start@bot_username
# formatidagi buyruqni ushlay olmaydi. Command("start") bu holatda ishonchliroq ishlaydi.
@router.message(Command("start"))
async def start_handler(message: Message, state: FSMContext, bot: Bot):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    first_name = message.from_user.first_name

    current_time = time.time()

    timestamps = START_COMMAND_LIMITS.get(user_id, [])
    timestamps = [t for t in timestamps if current_time - t < 60]  # 1 daqiqalik vaqt oralig'i
    timestamps.append(current_time)
    START_COMMAND_LIMITS[user_id] = timestamps

    # Check if user is already temp blocked from DB
    user_db = await db.get_user(user_id)
    if user_db and len(user_db) > 21 and user_db[21]: # temp_block_until is at index 21
        expire_time = datetime.fromisoformat(user_db[21]).timestamp()
        if current_time < expire_time:
            wait_time = int((expire_time - current_time) / 60) + 1
            msg = f"🚫 {first_name}, siz /start buyrug'ini juda tez-tez yuboryapsiz!\nBot {wait_time} daqiqaga vaqtincha bloklandi.\nIltimos kuting."
            await message.answer(msg, parse_mode="HTML")
            return

    # Agar 1 daqiqa ichida 10 martadan ko'p /start yuborilsa, 5 daqiqaga vaqtincha bloklanadi.
    if len(timestamps) > 5: # Reduced limit to 5 to be more strict
        temp_block_until = (datetime.now() + timedelta(minutes=5)).isoformat()
        await db.update_user_field(user_id, "temp_block_until", temp_block_until)
        START_COMMAND_LIMITS[user_id] = []  # Hisoblagichni tozalash
        
        # Unblock taskini ishga tushirish
        asyncio.create_task(send_unblock_notification(bot, user_id))
        
        lang = await get_user_lang(user_id)
        # Adminlarga xabar berish
        notify_text = get_text("admin_notify_flood", 'uz', user=escape(first_name), user_id=user_id)
        asyncio.create_task(notify_admins(bot, notify_text))
        
        msg = f"🚫 {first_name}, siz /start buyrug'ini juda tez-tez yuboryapsiz!\nBot 5 daqiqaga vaqtincha bloklandi.\nIltimos kuting."
        await message.answer(msg, parse_mode="HTML")
        return  # Handler ishini to'xtatish

    username = message.from_user.username or ""
    last_name = message.from_user.last_name or ""
    await db.log_action("Start", user_id, f"Username: {username}")
    is_admin = user_id in ADMIN_IDS or await db.is_user_admin(user_id)

    if is_admin:
        await state.clear()
        await message.answer(
            "Salom, Admin! 👑\nBosh menyuga xush kelibsiz! 🌟",
            reply_markup=main_menu_keyboard(is_admin=True, lang=lang, user_name=first_name),
        )
        return

    # Obuna tekshiruv (admin emas)
    missing = await check_subscription(bot, user_id)
    if missing:
        builder = InlineKeyboardBuilder()
        for ch in missing:
            channel_name = ch.replace("@", "")
            builder.add(
                InlineKeyboardButton(text=f"📢 {channel_name}", url=f"https://t.me/{channel_name}")
            )
        builder.add(InlineKeyboardButton(text="✅ Obuna bo'ldim", callback_data=f"check_sub_{user_id}")) # Guruxda adashmaslik uchun
        builder.adjust(1)
        await message.answer(
            f"Salom, {first_name}! 👋\nIltimos, quyidagi kanallarga obuna bo'ling 👇",
            reply_markup=builder.as_markup(),
        )
        return

    # 3. CAPTCHA tekshiruvi (Faqat obuna bo'lgandan keyin)
    if await db.needs_captcha(user_id):
        challenge, answer = await generate_captcha()
        await db.set_captcha(user_id, challenge, answer)
        await state.set_state(UserStates.captcha)
        await message.answer(f"Salom, {first_name}! 👋\nHavfsizlik tekshiruvi: {challenge} = ? 🔢")
    else:
        # Yangi sessiyani boshlash
        await state.clear()
        await state.update_data(session_start=time.time())
        
        # Profil borligini tekshirish va salomlashish
        user = await db.get_user(user_id)
        has_profile = await db.has_profile(user_id)
        
        # Agar profil bo'lsa to'liq ism, bo'lmasa telegram ism
        display_name = user[4] if (has_profile and user[4]) else first_name
        
        await message.answer(
            get_text("welcome_ready", lang, name=escape(display_name, quote=False)),
            reply_markup=main_menu_keyboard(lang=lang, user_name=display_name),
        )

    
@router.message(StateFilter(UserStates.captcha))
async def captcha_handler(message: Message, state: FSMContext, bot: Bot):
    """CAPTCHA javobini tekshirish"""
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    answer = (message.text or "").strip()

    captcha_data = await db.get_captcha(user_id)
    if not captcha_data:
        challenge, correct = await generate_captcha()
        await db.set_captcha(user_id, challenge, correct)
        await message.answer(f"🛡 Misolni yeching:\n\n<b>{challenge} = ?</b>", parse_mode="HTML")
        return

    if answer == captcha_data[1]:
        # Muvaffaqiyatli javobda xato hisoblagichni tozalash
        await db.update_user_field(user_id, "captcha_failures", 0)

        await db.update_last_captcha_time(user_id)
        await db.remove_captcha(user_id)
        await state.clear()

        # Ensure temp_block_until is cleared if it was set
        user_db = await db.get_user(user_id)
        if user_db and len(user_db) > 21 and user_db[21]:
            await db.update_user_field(user_id, "temp_block_until", None)

        user = await db.get_user(user_id)
        has_profile = await db.has_profile(user_id)
        name = user[4] if (has_profile and user[4]) else message.from_user.first_name
        is_admin = await is_user_admin(user_id)

        await message.answer(
            "✅ <b>To'g'ri!</b>\n" +
            get_text("welcome_ready", lang, name=escape(name, quote=False)),
            reply_markup=main_menu_keyboard(is_admin, lang, name),
            parse_mode="HTML"
        )
    else:
        # Xato urinishlar sonini oshirish
        user_db = await db.get_user(user_id)
        current_failures = user_db[20] if user_db and len(user_db) > 20 else 0 # captcha_failures is at index 20
        new_failures = current_failures + 1
        await db.update_user_field(user_id, "captcha_failures", new_failures)

        if new_failures >= 5: # Reduced limit to 5 for captcha
            # 5 daqiqaga bloklash
            temp_block_until = (datetime.now() + timedelta(minutes=5)).isoformat()
            await db.update_user_field(user_id, "temp_block_until", temp_block_until)
            await db.update_user_field(user_id, "captcha_failures", 0) # Reset failures
            await state.clear()

            # Blokdan chiqarish vazifasini rejalashtirish
            asyncio.create_task(unblock_and_show_menu(bot, user_id))

            # Adminga xabar berish
            notify_text = get_text("admin_notify_captcha_ban", 'uz', user=escape(message.from_user.first_name), user_id=user_id)
            asyncio.create_task(notify_admins(bot, notify_text))

            # Foydalanuvchiga xabar berish
            await message.answer("🚫 5 marta xato javob berildi. Siz 5 daqiqaga vaqtincha bloklandingiz.")
            return

        remaining_attempts = 5 - new_failures # Based on new limit
        challenge, correct = await generate_captcha()
        await db.set_captcha(user_id, challenge, correct)
        
        # Qolgan urinishlar soni bilan chiroyli xabar
        await message.answer(get_text("captcha_fail_attempts", lang, attempts=remaining_attempts, challenge=challenge), parse_mode="HTML")

# ============================================================
# Obuna tasdiqlash callback
# ============================================================
@router.callback_query(F.data.startswith("check_sub_"))
async def check_sub_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    target_user_id = int(callback.data.split("_")[2])
    
    # 0. Tugma egaligini tekshirish
    if user_id != target_user_id:
        await callback.answer("Bu tugma siz uchun emas! ❌", show_alert=True)
        return

    # 1. Avval obunani tekshiramiz
    missing = await check_subscription(bot, user_id)
    lang = await get_user_lang(user_id)

    if missing:
        await callback.answer("Hali obuna bo'lmagansiz! ⚠️", show_alert=True)
        return

    await callback.answer("Obuna tasdiqlandi! ✅")
    try:
        await callback.message.delete()
    except Exception:
        pass

    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user[4]) else callback.from_user.first_name
    is_admin = await is_user_admin(user_id)
    # 2. Agar obuna bo'lgan bo'lsa, keyin CAPTCHA tekshiramiz (if needed)
    if await db.needs_captcha(user_id):
        challenge, answer = await generate_captcha()
        await db.set_captcha(user_id, challenge, answer)
        await state.set_state(UserStates.captcha)
        await bot.send_message(user_id, f"🛡 <b>Xavfsizlik tekshiruvi!</b>\n\nBotdan foydalanish uchun misolni yeching:\n\n<b>{challenge} = ?</b>", parse_mode="HTML")
    else:
        await state.clear()
        await bot.send_message(
            user_id,
            get_text("welcome_ready", lang, name=escape(display_name, quote=False)),
            reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name),
        )

# ============================================================
# Reklama xizmatlari
# ============================================================
@router.callback_query(F.data == "menu_ads")
async def reklama_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await state.set_state(UserStates.ads_menu)
    await callback.message.edit_text(get_text("welcome_ads_name", lang, name=callback.from_user.first_name), reply_markup=ads_type_keyboard(lang))

@router.callback_query(StateFilter(UserStates.ads_menu), lambda c: c.data.startswith("ads_type_"))
async def ads_type_callback(callback: CallbackQuery, state: FSMContext):
    ads_type = callback.data.split("_")[2] # social or simple
    lang = await get_user_lang(callback.from_user.id)
    
    await state.update_data(ads_type=ads_type) # noqa
    
    if ads_type == "social":
        await state.set_state(UserStates.ads_platform)
        await callback.message.edit_text(get_text("ads_choose_platform", lang), reply_markup=ads_platform_keyboard(lang))
    else:
        # Oddiy matn reklamasi uchun platforma tanlash shart emas (yoki default)
        await state.update_data(ads_platform="simple_text")
        await state.set_state(UserStates.ads_text)
        await callback.message.edit_text(get_text("ads_enter_text", lang), reply_markup=cancel_keyboard(lang))

@router.callback_query(StateFilter(UserStates.ads_platform), lambda c: c.data.startswith("ads_plat_"))
async def ads_platform_callback(callback: CallbackQuery, state: FSMContext):
    platform = callback.data.split("_")[2] # instagram, telegram, all
    lang = await get_user_lang(callback.from_user.id)
    
    await state.update_data(ads_platform=platform) # noqa
    await state.set_state(UserStates.ads_text)
    await callback.message.edit_text(get_text("ads_enter_text", lang), reply_markup=cancel_keyboard(lang))

@router.message(StateFilter(UserStates.ads_text))
async def ads_text_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    await state.update_data(ads_text=message.text)

    await state.set_state(UserStates.ads_ask_media)
    await message.answer(get_text("ads_ask_media", lang), reply_markup=ads_media_ask_keyboard(lang))

@router.callback_query(StateFilter(UserStates.ads_ask_media), lambda c: c.data.startswith("ads_media_"))
async def ads_ask_media_callback(callback: CallbackQuery, state: FSMContext):
    choice = callback.data.split("_")[2] # yes or no
    lang = await get_user_lang(callback.from_user.id)
    
    if choice == "yes":
        await state.set_state(UserStates.ads_media)
        await callback.message.edit_text(get_text("ads_send_media", lang), reply_markup=cancel_keyboard(lang))
    else:
        await state.update_data(ads_media_id=None, ads_media_type=None) # noqa
        await show_ads_confirmation(callback.message, state, lang)

@router.message(StateFilter(UserStates.ads_media), F.content_type.in_([ContentType.PHOTO, ContentType.VIDEO, ContentType.DOCUMENT]))
async def ads_media_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    
    media_id = None
    media_type = None
    
    if message.photo:
        media_id = message.photo[-1].file_id
        media_type = "photo"
    elif message.video:
        media_id = message.video.file_id
        media_type = "video"
    elif message.document:
        media_id = message.document.file_id
        media_type = "document"

    await state.update_data(ads_media_id=media_id, ads_media_type=media_type)
    await show_ads_confirmation(message, state, lang)

async def show_ads_confirmation(message_obj: Message, state: FSMContext, lang: str):
    data = await state.get_data()
    ads_type = data.get("ads_type")
    platform = data.get("ads_platform")
    text = data.get("ads_text")
    media_type = data.get("ads_media_type")
    
    type_str = get_text("ads_type_social", lang) if ads_type == "social" else get_text("ads_type_simple", lang)
    
    plat_str = platform
    if platform == "instagram": plat_str = "Instagram"
    elif platform == "telegram": plat_str = "Telegram"
    elif platform == "all": plat_str = get_text("ads_platform_all", lang)
    elif platform == "simple_text": plat_str = "-"
    
    media_str = get_text("yes", lang) if media_type else get_text("no", lang)
    
    confirm_text = (
        f"{get_text('ads_confirm_title', lang)}\n\n"
        f"📌 Tur: {type_str}\n"
        f"📱 Platforma: {plat_str}\n"
        f"📎 Media: {media_str}\n"
        f"📝 Matn: {escape(text)}"
    )
    
    await state.set_state(UserStates.ads_confirm)
    await message_obj.answer(confirm_text, parse_mode="HTML", reply_markup=ads_confirm_keyboard(lang))

@router.callback_query(StateFilter(UserStates.ads_confirm), F.data == "ads_action_cancel")
async def ads_cancel_callback(callback: CallbackQuery, state: FSMContext):
    await go_to_main_menu(callback, state)

@router.callback_query(StateFilter(UserStates.ads_confirm), F.data == "ads_action_confirm")
async def ads_confirm_callback(callback: CallbackQuery, state: FSMContext, bot: Bot):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    data = await state.get_data()
    
    # Bazaga saqlash
    order_id = await db.add_order(
        user_id=user_id,
        order_text=data.get("ads_text"),
        order_type=data.get("ads_type"),
        platform=data.get("ads_platform"),
        media_file_id=data.get("ads_media_id"),
        media_type=data.get("ads_media_type")
    )
    
    await db.log_action("Ads Order", user_id, f"Order #{order_id} created")
    
    # Adminga faqat bildirishnoma yuborish
    # Foydalanuvchi ismini olish
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else callback.from_user.first_name
    for admin_id in ADMIN_IDS: # noqa
        try:
            # Admin uchun tilni aniqlash (yoki default 'uz')
            admin_lang = await get_user_lang(admin_id)
            await bot.send_message(admin_id, get_text("new_ad_order_admin", admin_lang, order_id=order_id))
        except Exception as e:
            logger.error(f"Adminga buyurtma yuborishda xato: {e}")

    await clear_state_preserve_session(state)
    await callback.message.edit_text(get_text("ads_order_sent", lang, name=display_name), reply_markup=main_menu_keyboard(lang=lang, user_name=display_name))

@router.callback_query(StateFilter(UserStates.ads_confirm), F.data == "ads_action_edit")
async def ads_edit_callback(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.ads_edit_select)
    await callback.message.edit_text(get_text("ads_edit_what", lang), reply_markup=ads_edit_select_keyboard(lang))

@router.callback_query(StateFilter(UserStates.ads_edit_select), lambda c: c.data.startswith("ads_edit_"))
async def ads_edit_selection(callback: CallbackQuery, state: FSMContext):
    target = callback.data.split("_")[2] # platform, media, text
    lang = await get_user_lang(callback.from_user.id)
    await state.update_data(ads_edit_target=target)
    await state.set_state(UserStates.ads_edit_input)
    
    if target == "platform":
        await callback.message.edit_text(get_text("ads_choose_platform", lang), reply_markup=ads_platform_keyboard(lang))
    elif target == "media":
        await callback.message.edit_text(get_text("ads_send_media", lang), reply_markup=cancel_keyboard(lang))
    elif target == "text":
        await callback.message.edit_text(get_text("ads_enter_text", lang), reply_markup=cancel_keyboard(lang))

@router.message(StateFilter(UserStates.ads_edit_input))
async def ads_edit_input_handler(message: Message, state: FSMContext):
    data = await state.get_data()
    target = data.get("ads_edit_target")
    lang = await get_user_lang(message.from_user.id)
    
    if target == "text":
        await state.update_data(ads_text=message.text)
    elif target == "media": # noqa
        # Media handling logic similar to ads_media_handler
        # ... (simplified for brevity, assume similar logic)
        pass 
    
    # Platform is handled via callback in ads_platform_callback logic if we reuse it or create specific edit callback
    # For simplicity, let's assume text/media edit asks for save
    await message.answer(get_text("ads_save_changes", lang), reply_markup=ads_save_changes_keyboard(lang))

@router.callback_query(lambda c: c.data == "ads_save_yes")
async def ads_save_yes(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await callback.answer(get_text("ads_saved", lang))
    await show_ads_confirmation(callback.message, state, lang)

@router.callback_query(lambda c: c.data == "ads_save_no")
async def ads_save_no(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await show_ads_confirmation(callback.message, state, lang)

# ============================================================
# Sozlamalar
# ============================================================
@router.callback_query(F.data == "menu_settings")
async def settings_handler(callback: CallbackQuery, state: FSMContext):
    """'Sozlamalar' tugmasi uchun handler. Til tanlash menyusini ko'rsatadi."""
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await state.set_state(UserStates.settings)
    await callback.message.edit_text(
        get_text("select_lang", lang),
        reply_markup=settings_language_keyboard(lang)
    )

@router.callback_query(F.data == "menu_music")
async def music_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    message = callback.message
    
    text = get_text("welcome_music_name", lang, name=callback.from_user.first_name)
    await safe_edit_message(callback, text, reply_markup=music_menu_keyboard(lang))
    await callback.answer()

@router.callback_query(F.data == "music_start_search")
async def music_start_search_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.music_search)
    text = get_text("enter_music_query_extended", lang)
    
    # Musiqa bo'limi tugmasini qo'shish
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    await callback.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())


# --- Shazam (Musiqa topish) ---
@router.callback_query(F.data == "music_shazam")
async def shazam_start_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.shazam_mode)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    
    await callback.message.edit_text(
        get_text("shazam_prompt", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.shazam_mode), F.content_type.in_([ContentType.VOICE, ContentType.AUDIO, ContentType.VIDEO, ContentType.VIDEO_NOTE]))
async def shazam_recognition_handler(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)

    file_obj = message.voice or message.audio or message.video or message.video_note

    # 20MB limit
    if file_obj.file_size > 20 * 1024 * 1024:
        await message.answer("⚠️ Fayl hajmi 20MB dan oshmasligi kerak! Iltimos, kichikroq fayl yuboring.", parse_mode="HTML")
        return

    status_msg = await message.answer(get_text("shazam_recognizing", lang), parse_mode="HTML")
    os.makedirs("downloads", exist_ok=True)

    unique_id = f"shazam_{user_id}_{int(time.time())}"
    # Fayl kengaytmasini aniqlash
    if message.voice: ext = "ogg"
    elif message.audio: ext = "mp3"
    elif message.video or message.video_note: ext = "mp4"
    else: ext = "dat"

    file_path = clean_path(f"downloads/{unique_id}.{ext}")

    try:
        # Faylni yuklab olish (faqat bot orqali, chunki 20MB limit bor)
        file_info = await message.bot.get_file(file_obj.file_id)
        await message.bot.download_file(file_info.file_path, destination=file_path)

        try:
            await status_msg.edit_text(get_text("shazam_recognizing", lang), parse_mode="HTML")
        except TelegramBadRequest:
            pass
            
        # Shazam
        if not SHAZAM_AVAILABLE:
            await status_msg.edit_text("⚠️ Shazam kutubxonasi mavjud emas. Iltimos, admin bilan bog'laning.")
            return
        shazam = Shazam()
        out = await shazam.recognize(file_path)
        track = out.get('track')

        if track:
            title = track.get('title', 'Unknown')
            subtitle = track.get('subtitle', 'Unknown')
            subtitle = subtitle.strip() or 'Unknown'

            await status_msg.edit_text(get_text("shazam_found_downloading", lang, title=title, artist=subtitle), parse_mode="HTML")

            search_variants = []
            if title and subtitle and subtitle != 'Unknown':
                search_variants.extend([
                    f"{title} {subtitle}",
                    f"{title} - {subtitle}",
                    f"{subtitle} {title}",
                ])
            if title:
                search_variants.append(title)
            if subtitle and subtitle != 'Unknown':
                search_variants.append(subtitle)

            info = None
            for search_query in search_variants:
                if not search_query:
                    continue
                for client in ['ios', 'android', 'web']:
                    try:
                        ydl_opts = {
                            'quiet': True,
                            'default_search': 'ytsearch1',
                            'noplaylist': True,
                            'skip_download': True,
                            'ignoreerrors': False,
                            'extractor_args': {'youtube': {'player_client': [client, 'web']}},
                        }
                        loop = asyncio.get_event_loop()
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = await loop.run_in_executor(None, lambda: ydl.extract_info(search_query, download=False))
                        if info and 'entries' in info and info['entries']:
                            break
                    except Exception as e:
                        logger.warning(f"Shazam qidiruv xatosi ({client}, query={search_query}): {e}")
                        continue
                if info and 'entries' in info and info['entries']:
                    break

            if info and 'entries' in info and info['entries']:
                video_id = info['entries'][0].get('id') or info['entries'][0].get('url')
                await _perform_music_download(message, video_id, user_id, message.bot, state, None, status_msg_to_use=status_msg)
            else:
                await status_msg.edit_text(get_text("not_found", lang), parse_mode="HTML")
        else:
            await status_msg.edit_text(get_text("shazam_not_found", lang), parse_mode="HTML")
            
    except Exception as e:
        logger.error(f"Shazam error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        await safe_remove(file_path)

# --- Videoni MP3 ga aylantirish ---
@router.callback_query(F.data == "video_to_mp3")
async def video_to_mp3_start(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.video_to_mp3)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    
    await callback.message.edit_text(
        get_text("video_to_mp3_prompt", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.video_to_mp3), F.content_type == ContentType.VIDEO)
async def video_to_mp3_process(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    # Telegram Bot API get_file orqali faqat 20MB gacha yuklay oladi.
    # 50MB gacha qo'llab-quvvatlash uchun Userbot kerak.
    if message.video.file_size > 50 * 1024 * 1024:
        await message.answer("⚠️ <b>Limitdan oshib ketdi!</b>\nIltimos, 50MB dan kichikroq video yuboring.", parse_mode="HTML")
        return
    
    if message.video.file_size > 20 * 1024 * 1024 and not user_bot:
        await message.answer("⚠️ <b>Texnik cheklov!</b>\nBot hozirda 20MB dan katta fayllarni Bot API orqali yuklab ololmaydi. Userbot faollashtirilmagan.")
        return

    if user_id in DOWNLOADING_USERS:
        return 

    status_msg = await message.answer(f"📥 {get_text('converting_video', lang)}", parse_mode="HTML")
    os.makedirs("downloads", exist_ok=True)
    DOWNLOADING_USERS.add(user_id)

    # 20MB dan katta bo'lsa Userbot bilan yuklash
    async def download_file(video_obj, path):
        if video_obj.file_size > 20 * 1024 * 1024:
            # Userbot orqali yuklash
            await user_bot.download_media(video_obj.file_id, file_name=path)
        else:
            # Standart bot orqali yuklash
            file_info = await message.bot.get_file(video_obj.file_id)
            await message.bot.download_file(file_info.file_path, destination=path)

    video = message.video
    file_info = await message.bot.get_file(video.file_id)
    
    unique_id = f"{user_id}_{int(time.time())}"
    downloaded_file_path = clean_path(f"downloads/{unique_id}.{file_info.file_path.split('.')[-1]}")
    final_mp3_path = clean_path(f"downloads/{unique_id}.mp3")

    try:
        # Faylni yuklab olish
        await download_file(video, downloaded_file_path)
        
        if not os.path.exists(downloaded_file_path):
            raise Exception("Video yuklab olinmadi.")

        process = await asyncio.create_subprocess_exec(
            'ffmpeg', '-i', downloaded_file_path, '-q:a', '0', '-map', 'a', final_mp3_path,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        _, stderr = await process.communicate()

        if process.returncode != 0:
            logger.error(f"FFMPEG xatosi: {stderr.decode()}")
            raise Exception("FFMPEG error")

        if os.path.exists(final_mp3_path):
            audio_file = FSInputFile(final_mp3_path)
            title = video.file_name or "O'girilgan audio"
            
            save_kb_builder = InlineKeyboardBuilder()
            save_kb_builder.add(InlineKeyboardButton(text=get_text("save_music", lang), callback_data="save_current_music"))
            save_kb_builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
            save_kb_builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            save_kb_builder.adjust(1)

            await message.answer_audio(audio_file, caption=f"🎵 <b>{title}</b>\n\n{get_text('converted_via_bot', lang, bot_username=(await message.bot.get_me()).username)}", parse_mode="HTML", reply_markup=save_kb_builder.as_markup())
            await status_msg.delete()
            await db.add_download_stat(user_id, "video_to_mp3")
        else:
            raise Exception("MP3 fayli yaratilmadi")
    except Exception as e:
        logger.error(f"Videoni MP3'ga o'girishda xato: {e}")
        await status_msg.edit_text(get_text("conversion_error", lang))
    finally:
        DOWNLOADING_USERS.discard(user_id)
        if os.path.exists(downloaded_file_path): os.remove(downloaded_file_path)
        if os.path.exists(final_mp3_path): os.remove(final_mp3_path)

# --- Ovoz va Matn Konverteri (TTS & STT) ---
@router.callback_query(F.data == "voice_to_text")
async def speech_converter_menu(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("voice_to_text_only_btn", lang), callback_data="stt_start"))
    builder.add(InlineKeyboardButton(text=get_text("text_to_voice_btn", lang), callback_data="tts_start"))
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    builder.adjust(1)
    
    await callback.message.edit_text(
        get_text("voice_to_text_prompt", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.callback_query(F.data == "stt_start")
async def stt_start_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.voice_to_text)
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    await callback.message.edit_text(
        get_text("send_voice_or_audio", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.voice_to_text), F.content_type.in_([ContentType.VOICE, ContentType.AUDIO]))
async def voice_to_text_process(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    # Sharh: Fayl hajmini tekshirish. Telegram botlari 20MB dan katta fayllarni yuklay olmaydi.
    file_to_check = message.voice or message.audio
    if file_to_check.file_size > 20 * 1024 * 1024:
        await message.answer(get_text("file_too_large_for_processing", lang))
        return

    status_msg = await message.answer("👂 <b>Eshitmoqdaman va yozmoqdaman...</b> ⏳", parse_mode="HTML")
    os.makedirs("downloads", exist_ok=True)
    
    unique_id = f"voice_{user_id}_{int(time.time())}"
    
    # Faylni aniqlash
    if message.voice:
        file_id = message.voice.file_id
        ext = "ogg"
    else:
        file_id = message.audio.file_id
        ext = "mp3"
        
    input_path = clean_path(f"downloads/{unique_id}.{ext}")
    wav_path = clean_path(f"downloads/{unique_id}.wav")
    
    loop = asyncio.get_event_loop()
    try:
        # 1. Yuklab olish
        file_info = await message.bot.get_file(file_id)
        await message.bot.download_file(file_info.file_path, destination=input_path)
        
        # 2. WAV formatga o'girish (SpeechRecognition uchun)
        def convert_and_recognize_sync():
            audio = AudioSegment.from_file(input_path)
            audio.export(wav_path, format="wav")
            
            # 3. Matnga aylantirish
            recognizer = sr.Recognizer()
            with sr.AudioFile(wav_path) as source:
                audio_data = recognizer.record(source)
                # Google Speech Recognition (Internet kerak)
                return recognizer.recognize_google(audio_data, language="uz-UZ")

        text = await loop.run_in_executor(None, convert_and_recognize_sync)
            
        await status_msg.edit_text(f"📝 <b>Natija:</b>\n\n{escape(text)}", parse_mode="HTML")
        
    except sr.UnknownValueError:
        await status_msg.edit_text("⚠️ Kechirasiz, ovozni tushuna olmadim. Aniqroq gapirib ko'ring.")
    except sr.RequestError as e:
        logger.error(f"SpeechRecognition xatosi: {e}")
        await status_msg.edit_text("⚠️ Server bilan bog'lanishda xatolik.")
    except Exception as e:
        logger.error(f"Ovoz->Matn xatosi: {e}")
        await status_msg.edit_text("⚠️ Kutilmagan xatolik yuz berdi.")
    finally:
        if os.path.exists(input_path): os.remove(input_path)
        if os.path.exists(wav_path): os.remove(wav_path)

@router.callback_query(F.data == "tts_start")
async def tts_start_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.text_to_voice)
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    await callback.message.edit_text(
        get_text("text_to_voice_prompt", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.text_to_voice))
async def tts_ask_gender(message: Message, state: FSMContext):
    text = message.text
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    if not text:
        await message.answer("Iltimos, matn yuboring.")
        return
    
    # Matnni saqlab qo'yamiz
    await state.update_data(tts_text=text)
    
    # Ovoz turini tanlash uchun tugmalar
    builder = InlineKeyboardBuilder() # noqa
    builder.add(InlineKeyboardButton(text=get_text("voice_male", lang), callback_data="tts_gender_male"))
    builder.add(InlineKeyboardButton(text=get_text("voice_female", lang), callback_data="tts_gender_female"))
    builder.adjust(2)
    builder.row(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
    
    await message.answer(get_text("select_voice_gender", lang), parse_mode="HTML", reply_markup=builder.as_markup())
    await state.set_state(UserStates.tts_voice_select)

@router.callback_query(StateFilter(UserStates.tts_voice_select), lambda c: c.data.startswith("tts_gender_"))
async def tts_process_callback(callback: CallbackQuery, state: FSMContext):
    gender = callback.data.split("_")[2] # male or female
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    
    data = await state.get_data()
    text = data.get("tts_text")
    
    await callback.message.delete() # Tanlov xabarini o'chirish
    status_msg = await callback.message.answer(get_text("converting_to_voice", lang), parse_mode="HTML")
    
    os.makedirs("downloads", exist_ok=True)
    unique_id = f"tts_{user_id}_{int(time.time())}.mp3"
    file_path = clean_path(f"downloads/{unique_id}")
    
    try:
        # Ovozni tanlash
        if lang == 'uz': # noqa
            voice = "uz-UZ-SardorNeural" if gender == "male" else "uz-UZ-MadinaNeural"
        elif lang == 'ru':
            voice = "ru-RU-DmitryNeural" if gender == "male" else "ru-RU-SvetlanaNeural"
        else: # en
            voice = "en-US-GuyNeural" if gender == "male" else "en-US-JennyNeural"

        communicate = edge_tts.Communicate(text, voice)
        await communicate.save(file_path)

        audio_file = FSInputFile(file_path)
        new_caption = f"📝 Matn: {escape(text[:50])}...\n\n{get_text('tts_send_next', lang)}"

        # Tugmalarni qo'shish
        builder = InlineKeyboardBuilder()
        builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
        builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        builder.adjust(1) # noqa

        await callback.message.answer_voice(audio_file, caption=new_caption, reply_markup=builder.as_markup(), parse_mode="HTML")
        await status_msg.delete()
        
        # Yana matn yuborish uchun holatni qaytarish (Loop)
        # Sharh: Bu yerda holat qayta o'rnatiladi, lekin ortiqcha xabar yuborilmaydi.
        await state.set_state(UserStates.text_to_voice)
    except Exception as e:
        logger.error(f"TTS xatosi: {e}")
        await status_msg.edit_text("⚠️ Xatolik yuz berdi.")
    finally:
        if os.path.exists(file_path): os.remove(file_path)

# --- Universal Shazam Handler (Video/Audio xabardan) ---
@router.callback_query(F.data == "find_music_from_msg")
async def find_music_from_msg_callback(callback: CallbackQuery, state: FSMContext):
    """Xabardagi media (video/audio) orqali musiqani topish va to'liq yuklash"""
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    message = callback.message

    # Media faylni aniqlash
    file_obj = message.video or message.audio or message.voice or message.video_note
    if not file_obj:
        await callback.answer("Media fayl topilmadi.", show_alert=True)
        return
    
    # 20MB limit
    if file_obj.file_size > 20 * 1024 * 1024:
        await callback.answer("⚠️ Fayl hajmi 20MB dan oshmasligi kerak!", show_alert=True)
        return

    await callback.answer("Musiqa qidirilmoqda... 🎧")
    status_msg = await message.reply(get_text("shazam_recognizing", lang), parse_mode="HTML")

    os.makedirs("downloads", exist_ok=True)
    unique_id = f"shazam_cb_{user_id}_{int(time.time())}"
    file_path = clean_path(f"downloads/{unique_id}.tmp")

    try:
        # Faylni yuklab olish
        file_info = await callback.bot.get_file(file_obj.file_id)
        await callback.bot.download_file(file_info.file_path, destination=file_path)

        try:
            await status_msg.edit_text(get_text("shazam_recognizing", lang), parse_mode="HTML")
        except TelegramBadRequest:
            pass
            # Shazam
        shazam = Shazam()
        out = await shazam.recognize(file_path)
        track = out.get('track')

        if track:
            title = track.get('title', 'Unknown')
            subtitle = track.get('subtitle', 'Unknown')
            # Yangi formatdagi xabar
            await status_msg.edit_text(get_text("shazam_found_downloading", lang, title=title, artist=subtitle), parse_mode="HTML")

            # Musiqani yuklash
            search_query = f"{title} {subtitle}"
            
            # 🚀 Optimallashtirish: Ro'yxat chiqarmasdan, to'g'ridan-to'g'ri birinchi natijani yuklash (Retry bilan)
            clients_to_try = YOUTUBE_PLAYER_CLIENTS
            info = None
            loop = asyncio.get_event_loop()
            
            for client in clients_to_try:
                try:
                    ydl_opts = {
                        'quiet': True, 'default_search': 'ytsearch1', 'noplaylist': True, 'skip_download': True,
                        'ignoreerrors': False,
                        'extractor_args': {'youtube': {'player_client': [client, 'web']}},
                    }
                    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                        info = await loop.run_in_executor(None, lambda: ydl.extract_info(search_query, download=False))
                    
                    if info and 'entries' in info and info['entries']:
                        break
                except Exception as e:
                    logger.warning(f"Universal Shazam qidiruv xatosi ({client}): {e}")
                    continue
            
            if info and 'entries' in info and info['entries']:
                video_id = info['entries'][0]['id']
                # To'g'ridan-to'g'ri yuklash funksiyasini chaqiramiz
                await _perform_music_download(message, video_id, user_id, callback.bot, state, callback, status_msg_to_use=status_msg, query_from_shazam=True)
            else:
                await status_msg.edit_text(get_text("not_found", lang))
        else:
            await status_msg.edit_text(get_text("shazam_not_found", lang))

    except Exception as e:
        logger.error(f"Universal Shazam error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        await safe_remove(file_path)

# --- Musiqa qidirish (Optimallashtirilgan) ---
@router.message(StateFilter(UserStates.music_search))
async def music_search_perform(message: Message, state: FSMContext, query_text: str = None, bot_instance: Bot = None):
    # Agar query_text berilgan bo'lsa (Shazamdan), o'shani ishlatamiz, aks holda message.text
    query = query_text if query_text else message.text
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    # Bot instansiyasini aniqlash
    bot = bot_instance if bot_instance else message.bot
    
    # Agar havola yuborilsa, jim turamiz (foydalanuvchi so'rovi bo'yicha)
    if YOUTUBE_PATTERN.search(query) or INSTAGRAM_PATTERN.search(query):
        return

    # 1. Animatsiya bilan qidiruv xabarini yuborish
    if bot_instance:
        status_msg = await bot.send_message(message.chat.id, get_text("searching_music", lang, name=message.from_user.first_name), parse_mode="HTML")
    else:
        status_msg = await message.answer(get_text("searching_music", lang, name=message.from_user.first_name), parse_mode="HTML")
    
    try:
        # 3. Youtube'dan ma'lumot olish (kuchaytirilgan cookie mantig'i bilan)
        auth_sources_to_try = youtube_auth_sources()
        last_exception = None
        info = None

        for auth_source in auth_sources_to_try:
            try:
                ydl_opts = {
                    'quiet': True,
                    'default_search': 'ytsearch10',  # 20 ta kifoya
                    'noplaylist': True,
                    'extract_flat': "in_playlist",
                    'skip_download': True, 
                    'add_metadata': False,
                    'ignoreerrors': True,
                    'source_address': '0.0.0.0', # IPv4 forcelash
                    'http_headers': {
                        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
                        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
                        'Accept-Language': 'en-us,en;q=0.5',
                        'Sec-Fetch-Mode': 'navigate',
                    },
                    'sleep_interval': 2,
                    'extractor_args': {
                        'youtube': {
                            'player_client': YOUTUBE_PLAYER_CLIENTS,
                        }
                    },
                    'max_sleep_interval': 4,
                    'retries': 3,
                    'fragment_retries': 3,
                    'ratelimit': None,
                }
                apply_youtube_auth(ydl_opts, auth_source)
                source_type, source_value = auth_source
                logger.info("Qidiruv uchun autentifikatsiya sinovi: %s", os.path.basename(source_value) if source_type == "file" else source_value or "cookiesiz")

                loop = asyncio.get_event_loop()
                with yt_dlp.YoutubeDL(ydl_opts) as ydl: # type: ignore
                    info = await loop.run_in_executor(None, lambda: ydl.extract_info(f"ytsearch10:{query}", download=False))
                
                if info is None:
                    logger.error("⚠️ YouTube qidiruvda ma'lumot qaytarilmadi. Manba: %s", auth_source)
                    continue
                
                # Agar muvaffaqiyatli bo'lsa, tsiklni to'xtatish
                if info and info.get('entries'):
                    logger.info(f"✅ Qidiruv muvaffaqiyatli: {len(info['entries'])} natija topildi.")
                    break

            except yt_dlp.utils.DownloadError as e:
                last_exception = e
                if "Sign in to confirm" in str(e) or "authentication" in str(e):
                    logger.warning("Qidiruvda autentifikatsiya xatosi (%s). Keyingisi sinab ko'riladi.", auth_source)
                    continue
                else:
                    # Boshqa xato, tsiklni to'xtatish
                    break

        if info and 'entries' in info and info['entries']:
            # Natijalarni tozalash (bo'shlarini olib tashlash)
            items = [e for e in info['entries'] if e]
            
            # Natijalarni holat (state) da saqlaymiz
            await state.update_data(music_results=items)
            
            # Birinchi sahifani ko'rsatish
            await show_music_page(status_msg, items, 0, lang)
        else:
            # Agar barcha urinishlar muvaffaqiyatsiz bo'lsa
            if last_exception:
                raise last_exception # Xatoni yuqoriga uzatish
            else:
                await status_msg.edit_text(get_text("not_found", lang))

    except Exception as e:
        logger.error(f"YouTube qidiruv xatosi: {e}", exc_info=True)
        await status_msg.edit_text(get_text("error", lang))

# --- Video Bo'limi (Yangi) ---
@router.callback_query(F.data == "menu_video")
async def video_menu_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)

    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("my_videos", lang), callback_data="menu_my_videos"))
    builder.add(InlineKeyboardButton(text=get_text("round_video_btn", lang), callback_data="video_mode_round"))
    builder.add(InlineKeyboardButton(text=get_text("video_link_btn", lang), callback_data="video_mode_link"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1) # noqa
    
    text = get_text("welcome_video_name", lang, name=callback.from_user.first_name)
    
    await safe_edit_message(callback, text, reply_markup=builder.as_markup())

@router.callback_query(F.data == "video_mode_link")
async def video_link_mode_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.video_download)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    
    await callback.message.edit_text(
        get_text("video_link_prompt_extended", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.video_download))
async def video_download_perform(message: Message, state: FSMContext):
    query = message.text
    user_id = message.from_user.id
    lang = await get_user_lang(message.from_user.id)
    
    # 1. YouTube havolasini tekshirish
    yt_match = YOUTUBE_PATTERN.search(query)
    if yt_match: # Agar havola bo'lsa
        if user_id in DOWNLOADING_USERS:
            return # Jim turamiz (foydalanuvchi talabi)
            
        video_id = yt_match.group(1)
        # Agar Shorts bo'lsa, sifat so'ramasdan to'g'ridan-to'g'ri yuklaymiz
        if "shorts" in query.lower():
            await _perform_youtube_download(message, video_id, user_id, message.bot, hide_title=False, is_shorts=True)
            return

        # Oddiy video bo'lsa, formatni so'raymiz
        await message.answer(
            get_text("yt_video_found", lang),
            parse_mode="HTML",
            reply_markup=youtube_format_keyboard(video_id, lang)
        )
        return

    # 2. Instagram havolasini tekshirish
    insta_match = INSTAGRAM_PATTERN.search(query) # Instagram havola
    if insta_match:
        if user_id in DOWNLOADING_USERS:
            return # Jim turamiz
            
        shortcode = insta_match.group(2)
        await download_instagram_media(message, query, shortcode)
        return

    # 3. Facebook havolasini tekshirish
    if FACEBOOK_PATTERN.search(query):
        if user_id in DOWNLOADING_USERS:
            return # Jim turamiz
            
        await _perform_generic_video_download(message, query, user_id, message.bot)
        return

    # Agar havola bo'lmasa
    await message.answer("⚠️ Iltimos, to'g'ri YouTube, Instagram yoki Facebook havolasini yuboring.")

# --- Dumaloq Video (Video Note) ---
@router.callback_query(F.data == "video_mode_round")
async def round_video_mode_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.round_video)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    
    await callback.message.edit_text(
        get_text("round_video_prompt", lang),
        parse_mode="HTML",
        reply_markup=builder.as_markup()
    )

@router.message(StateFilter(UserStates.round_video), F.content_type == ContentType.VIDEO)
async def round_video_process(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    # Sharh: Fayl hajmini tekshirish. Telegram botlari 20MB dan katta fayllarni yuklay olmaydi.
    if message.video.file_size > 20 * 1024 * 1024:
        await message.answer(get_text("file_too_large_for_processing", lang))
        return

    status_msg = await message.answer(get_text("converting_round", lang), parse_mode="HTML")
    os.makedirs("downloads", exist_ok=True)
    
    video = message.video
    file_info = await message.bot.get_file(video.file_id)
    
    unique_id = f"round_{user_id}_{int(time.time())}"
    input_path = clean_path(f"downloads/{unique_id}.mp4")
    output_path = clean_path(f"downloads/{unique_id}_round.mp4")

    await message.bot.download_file(file_info.file_path, destination=input_path)
    
    # Bot username'ini olish (suv belgisi uchun)
    bot_username = (await message.bot.get_me()).username

    try:
        # FFmpeg: Markazdan qirqish (crop) va 640x640 o'lchamga keltirish
        # crop='min(iw,ih)':'min(iw,ih)' -> eng kichik tomon bo'yicha kvadrat qirqish
        # scale=640:640 -> Telegram video note standarti
        # Sifatni saqlash uchun CRF 23 va preset fast ishlatamiz (Suv belgisi olib tashlandi)
        process = await asyncio.create_subprocess_exec(
            'ffmpeg', '-i', input_path, 
            '-vf', "crop='min(iw,ih)':'min(iw,ih)',scale=640:640", 
            '-c:v', 'libx264', '-preset', 'fast', '-crf', '23', '-c:a', 'aac', '-b:a', '128k', '-t', '60', # Max 1 min
            output_path,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        _, stderr = await process.communicate()

        if os.path.exists(output_path):
            video_note = FSInputFile(output_path)
            
            # Tugmalarni qo'shish
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text=get_text("save_video", lang), callback_data="save_current_video"))
            builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
            builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            builder.adjust(1) # Vertikal tugmalar
            
            await message.answer_video_note(video_note, reply_markup=builder.as_markup())
            await status_msg.delete()
        else:
            raise Exception("Output file not created")
            
    except Exception as e:
        logger.error(f"Round video error: {e}")
        await status_msg.edit_text(get_text("round_video_error", lang))
    finally:
        if os.path.exists(input_path): os.remove(input_path)
        if os.path.exists(output_path): os.remove(output_path)

# --- Rasm Bo'limi (Yangi) ---
@router.callback_query(F.data == "menu_image")
async def image_menu_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.image_menu)
    
    text = get_text("welcome_image_name", lang, name=callback.from_user.first_name)
    await safe_edit_message(callback, text, reply_markup=image_menu_keyboard(lang))

@router.callback_query(F.data.startswith("img_"))
async def image_action_handler(callback: CallbackQuery, state: FSMContext):
    action = callback.data
    lang = await get_user_lang(callback.from_user.id)
    
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("back_to_images", lang), callback_data="menu_image"))
    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)
    
    if action == "img_rm_bg": # noqa
        await state.set_state(UserStates.image_rm_bg)
        text = get_text("send_photo_bg", lang)
    elif action == "img_filter":
        await state.set_state(UserStates.image_filter)
        text = get_text("send_photo_filter", lang)
    
    await callback.message.edit_text(text, reply_markup=builder.as_markup())

@router.message(StateFilter(UserStates.image_rm_bg, UserStates.image_filter), F.content_type == ContentType.PHOTO)
async def process_image_handler(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    current_state = await state.get_state()
    
    # Sharh: Fayl hajmini tekshirish. Telegram botlari 20MB dan katta fayllarni yuklay olmaydi.
    # Rasm uchun bu kamdan-kam hollarda bo'ladi, lekin xavfsizlik uchun qo'shildi.
    if message.photo[-1].file_size > 20 * 1024 * 1024:
        await message.answer(get_text("file_too_large_for_processing", lang))
        return

    status_msg = await message.answer(get_text("processing_image", lang), parse_mode="HTML")
    os.makedirs("downloads", exist_ok=True)
    
    unique_id = f"img_{user_id}_{int(time.time())}"
    input_path = clean_path(f"downloads/{unique_id}.jpg")
    output_path = clean_path(f"downloads/{unique_id}_out.png")
    
    loop = asyncio.get_event_loop()
    try:
        # Rasmni yuklab olish
        photo = message.photo[-1]
        await message.bot.download(photo, destination=input_path)
        
        def process_sync():
            img = Image.open(input_path)
            if current_state == UserStates.image_rm_bg:
                if not REMBG_AVAILABLE:
                    return None # Signal that it failed
                output = remove_bg(img)
                output.save(output_path, "PNG")
            elif current_state == UserStates.image_filter:
                img = ImageOps.grayscale(img)
                img.save(output_path, "PNG")
            return True # Signal success

        result = await loop.run_in_executor(None, process_sync)
        if not result:
            await safe_remove(input_path)
            await status_msg.edit_text(get_text("rembg_not_installed", lang))
            return
            
        # Natijani yuborish
        result_file = FSInputFile(output_path)
        bot_username = (await message.bot.get_me()).username
        caption = get_text("processed_via_bot", lang, bot_username=bot_username)
        
        builder = InlineKeyboardBuilder()
        builder.add(InlineKeyboardButton(text=get_text("save_image", lang), callback_data="save_current_image"))
        builder.add(InlineKeyboardButton(text=get_text("back_to_images", lang), callback_data="menu_image"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        
        await message.answer_document(result_file, caption=caption, reply_markup=builder.as_markup())
        await status_msg.delete()
        
    except Exception as e:
        logger.error(f"Image processing error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        if os.path.exists(input_path): os.remove(input_path)
        if os.path.exists(output_path): os.remove(output_path)

@router.callback_query(F.data.startswith("yt_audio_from_video_"))
async def yt_audio_from_video_callback(callback: CallbackQuery, state: FSMContext):
    """YouTube videosidan audioni ajratib olish (Shazam emas, to'g'ridan-to'g'ri yuklash)"""
    video_id = callback.data[20:] # "yt_audio_from_video_" (20 chars)
    user_id = callback.from_user.id
    # Musiqa yuklash funksiyasini chaqiramiz (bu funksiya audio yuklaydi)
    await _perform_music_download(callback.message, video_id, user_id, callback.bot, state, callback)

@router.callback_query(F.data.startswith("yt_fmt_"))
async def youtube_format_callback(callback: CallbackQuery, state: FSMContext):
    parts = callback.data.split("_")
    fmt = parts[2] # mp3 or video
    video_id = "_".join(parts[3:]) # ID tarkibida _ bo'lsa ham to'g'ri olish
    lang = await get_user_lang(callback.from_user.id)
    
    if fmt == "mp3":
        # MP3 yuklashni boshlash (yangi yordamchi funksiya orqali)
        await _perform_music_download(callback.message, video_id, callback.from_user.id, callback.bot, state, callback)
    elif fmt == "video":
        # Video sifatini tanlash
        await callback.message.edit_text(get_text("choose_video_quality", lang), parse_mode="HTML", reply_markup=youtube_resolution_keyboard(video_id, lang))

@router.callback_query(lambda c: c.data.startswith("yt_dl_res_"))
async def youtube_resolution_callback(callback: CallbackQuery):
    parts = callback.data.split("_")
    resolution = parts[-1] # Oxirgi qism har doim resolution
    video_id = "_".join(parts[3:-1]) # Qolgan qismi ID (tarkibida _ bo'lishi mumkin)
    user_id = callback.from_user.id
    
    # Kodni takrorlamaslik uchun umumiy funksiyaga yo'naltiramiz
    await _perform_youtube_download(callback.message, video_id, user_id, callback.bot, resolution, callback, is_shorts=False)

@router.callback_query(F.data.startswith("yt_shazam_full_"))
async def yt_shazam_full_callback(callback: CallbackQuery, state: FSMContext):
    """YouTube videosidan musiqani aniqlab, to'liq versiyasini yuklash"""
    video_id = callback.data[15:] # "yt_shazam_full_" (15 chars)
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)

    await callback.answer("Musiqa qidirilmoqda... 🎧")
    status_msg = await callback.message.answer(get_text("shazam_recognizing", lang), parse_mode="HTML")
    
    os.makedirs("downloads", exist_ok=True)
    unique_id = f"yt_shazam_{user_id}_{int(time.time())}"
    temp_audio_path = clean_path(f"downloads/{unique_id}.mp3")

    try:
        # 1. Videoning audiosini yuklab olish (Shazam uchun)
        loop = asyncio.get_event_loop()
        ydl_opts = {
            'format': 'bestaudio/best',
            'outtmpl': temp_audio_path,
            'extractor_args': {'youtube': {
                'player_client': YOUTUBE_PLAYER_CLIENTS,
                'remote_components': 'ejs:github' # Masofaviy JS yechuvchi
            }},
            'quiet': True, 'ignoreerrors': True, # Qayta urinish uchun ignoreerrors
            'noplaylist': True,
            'source_address': '0.0.0.0',
        }
        apply_youtube_auth(ydl_opts, youtube_auth_sources()[0])
        
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            await loop.run_in_executor(None, lambda: ydl.download([f"https://www.youtube.com/watch?v={video_id}"]))
            
        # Agar mp3 bo'lmasa, m4a yoki boshqa formatda bo'lishi mumkin, nomini to'g'rilash
        if not os.path.exists(temp_audio_path):
            # yt-dlp ba'zan kengaytmani o'zgartiradi, shuning uchun papkani tekshiramiz
            base_name = temp_audio_path.rsplit('.', 1)[0]
            for ext in ['m4a', 'webm', 'opus', 'mp3']:
                potential_path = f"{base_name}.{ext}"
                if os.path.exists(potential_path):
                    temp_audio_path = potential_path
                    break

        if not os.path.exists(temp_audio_path):
            raise Exception("Audio yuklanmadi")

        # 2. Shazam orqali aniqlash
        if not SHAZAM_AVAILABLE:
            await status_msg.edit_text("⚠️ Shazam kutubxonasi mavjud emas. Iltimos, admin bilan bog'laning.")
            return
        shazam = Shazam()
        out = await shazam.recognize(temp_audio_path)
        track = out.get('track') if out else None

        if track:
            title = track.get('title', 'Unknown')
            subtitle = track.get('subtitle', 'Unknown')
            
            # 3. Topilgan musiqani xabar qilish
            await status_msg.edit_text(get_text("shazam_found_downloading", lang, title=title, artist=subtitle), parse_mode="HTML")
            
            # 4. To'liq versiyani qidirish va yuklash
            search_query = f"{title} {subtitle}"
            
            # Qidiruv uchun yt-dlp ishlatamiz (Retry bilan)
            clients_to_try = YOUTUBE_PLAYER_CLIENTS
            info_search = None
            
            for client in clients_to_try:
                try:
                    ydl_opts_search = {'quiet': True, 'default_search': 'ytsearch1', 'noplaylist': True, 'skip_download': True, 'ignoreerrors': False}
                    with yt_dlp.YoutubeDL(ydl_opts_search) as ydl_search:
                        ydl_search.params['extractor_args'] = {'youtube': {'player_client': [client, 'web']}}
                        info_search = await loop.run_in_executor(None, lambda: ydl_search.extract_info(search_query, download=False))
                    
                    if info_search and 'entries' in info_search and info_search['entries']:
                        if info_search is None:
                            raise DownloadError("Failed to extract search info for YouTube Shazam.")
                        break
                except Exception as e:
                    logger.warning(f"YouTube Shazam qidiruv xatosi ({client}): {e}")
                    continue
            
            if info_search and 'entries' in info_search and info_search['entries']:
                full_video_id = info_search['entries'][0]['id']
                await _perform_music_download(callback.message, full_video_id, user_id, callback.bot, state, callback, status_msg_to_use=status_msg, query_from_shazam=True)
            else:
                await status_msg.edit_text(get_text("not_found", lang))
        else:
            await status_msg.edit_text(get_text("shazam_not_found", lang))
    except Exception as e:
        logger.error(f"YouTube Shazam error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        if os.path.exists(temp_audio_path): os.remove(temp_audio_path)


async def show_music_page(message_obj: Message, items: list, page: int, lang: str):
    """Musiqa natijalarini sahifalab ko'rsatish funksiyasi"""
    ITEMS_PER_PAGE = 10
    total_pages = (len(items) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
    
    start_idx = page * ITEMS_PER_PAGE
    end_idx = start_idx + ITEMS_PER_PAGE
    current_items = items[start_idx:end_idx]
    
    # Chiroyli ro'yxat tuzish
    text = get_text("search_results_header", lang, page=page+1) + "\n\n"
    for idx, item in enumerate(current_items):
        title = item.get('title', get_text("lbl_none", lang))
        # HTML belgilarini tozalash
        title = escape(title)
        
        # Duration qo'shish
        duration = item.get('duration')
        duration_str = ""
        filesize_str = ""

        if duration:
            try:
                seconds = int(duration)
                m, s = divmod(seconds, 60)
                if m >= 60:
                    h, m = divmod(m, 60)
                    duration_str = f" <i>({h}:{m:02d}:{s:02d})</i>"
                else:
                    duration_str = f" <i>({m:02d}:{s:02d})</i>"
                
                # Hajmni hisoblash (taxminan 128kbps = 16 KB/s)
                approx_mb = (seconds * 16) / 1024
                filesize_str = f" 💾 ~{approx_mb:.1f} MB"
            except (ValueError, TypeError):
                pass

        # Agar aniq hajm bo'lsa (yt_dlp ba'zida beradi)
        filesize = item.get('filesize') or item.get('filesize_approx')
        if filesize:
            try:
                mb = filesize / (1024 * 1024)
                filesize_str = f" 💾 {mb:.1f} MB"
            except: pass

        text += f"<b>{idx + 1}.</b> {title}{duration_str}{filesize_str}\n"
    
    text += f'\n{get_text("press_to_download", lang)}'
    
    keyboard = music_results_keyboard(current_items, page, total_pages, len(items), lang)
    
    try:
        await message_obj.edit_text(text, parse_mode="HTML", reply_markup=keyboard)
    except TelegramBadRequest:
        # Agar xabar o'zgarmagan bo'lsa yoki eski bo'lsa
        await message_obj.answer(text, parse_mode="HTML", reply_markup=keyboard)

@router.callback_query(F.data.startswith("music_page_"))
async def music_pagination_callback(callback: CallbackQuery, state: FSMContext):
    """Sahifalash tugmalari bosilganda ishlaydi"""
    page = int(callback.data.split("_")[2])
    data = await state.get_data()
    items = data.get("music_results", [])
    lang = await get_user_lang(callback.from_user.id)
    
    if not items:
        await callback.answer("Natijalar eskirgan, qayta qidiring.", show_alert=True)
        return

    await show_music_page(callback.message, items, page, lang)
    await callback.answer()

@router.callback_query(F.data.startswith("insta_shazam_music_"))
async def insta_shazam_music_callback(callback: CallbackQuery, state: FSMContext):
    shortcode = callback.data.split("_")[3] # insta_shazam_music_{shortcode}
    url = f"https://www.instagram.com/p/{shortcode}/"
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)

    if user_id in DOWNLOADING_USERS:
        await callback.answer(get_text("download_in_progress_alert", lang), show_alert=True)
        return

    await callback.answer("Musiqa topilmoqda... 🎧")
    status_msg = await callback.message.answer(get_text("shazam_recognizing", lang), parse_mode="HTML")
    DOWNLOADING_USERS.add(user_id)

    os.makedirs("downloads", exist_ok=True)
    unique_id = f"insta_shazam_{shortcode}_{int(time.time())}"
    audio_file_path = clean_path(f"downloads/{unique_id}.mp3")

    try:
        loop = asyncio.get_event_loop()
        last_update_time = [time.time()]
        downloaded_files = []
        def insta_progress_hook(d):
            progress_hook(d, callback.bot, status_msg, last_update_time, loop, lang, finished_text_key="music_almost_ready")
            if d.get('status') == 'finished' and d.get('filename'):
                downloaded_files.append(clean_path(d['filename']))

        ydl_opts = {
            'format': 'bestaudio/best',
            'outtmpl': audio_file_path,
            'postprocessors': [{
                'key': 'FFmpegExtractAudio',
                'preferredcodec': 'mp3',
                'preferredquality': '192',
            }],
            'quiet': True,
            'geo_bypass': True,
            'cookiefile': INSTAGRAM_COOKIES_PATH,
            'ignoreerrors': True,
            'retries': 10,
            'source_address': '0.0.0.0',
            'buffersize': 1024 * 1024 * 10,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)',
            },
            'sleep_interval': 3,
            'max_sleep_interval': 5,
            'progress_hooks': [insta_progress_hook],
        }
        
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = await loop.run_in_executor(None, lambda: ydl.extract_info(url, download=True))
            actual_audio_filename = clean_path(ydl.prepare_filename(info).rsplit(".", 1)[0] + ".mp3")

        if not os.path.exists(actual_audio_filename):
            raise Exception("Audio fayl yuklab olinmadi.")

        # Shazam orqali aniqlash
        if not SHAZAM_AVAILABLE:
            await status_msg.edit_text("⚠️ Shazam kutubxonasi mavjud emas. Iltimos, admin bilan bog'laning.")
            return
        shazam = Shazam()
        out = await shazam.recognize(actual_audio_filename)
        
        track = out.get('track') if out else None
        if track:
            title = track.get('title')
            subtitle = track.get('subtitle') # Artist
            
            await status_msg.edit_text(get_text("shazam_found_downloading", lang, title=title, artist=subtitle), parse_mode="HTML")
            
            # Musiqani qidirish va yuklash
            search_query = f"{title} {subtitle}"
            
            # Qidiruv uchun yt-dlp ishlatamiz (Retry bilan)
            clients_to_try = YOUTUBE_PLAYER_CLIENTS
            info_search = None
            
            for client in clients_to_try:
                try:
                    ydl_opts_search = {
                        'quiet': True, 'default_search': 'ytsearch1', 'noplaylist': True, 'skip_download': True, 'ignoreerrors': False,
                        'extractor_args': {'youtube': {
                            'player_client': YOUTUBE_PLAYER_CLIENTS,
                            'remote_components': 'ejs:github' # Masofaviy JS yechuvchi
                        }},
                    }
                    with yt_dlp.YoutubeDL(ydl_opts_search) as ydl_search:
                        info_search = await loop.run_in_executor(None, lambda: ydl_search.extract_info(search_query, download=False))
                    
                    if info_search and 'entries' in info_search and info_search['entries']:
                        if info_search is None:
                            raise DownloadError("Failed to extract search info for Shazam.")
                        break
                except Exception as e:
                    logger.warning(f"Instagram Shazam qidiruv xatosi ({client}): {e}")
                    continue
                
            if info_search and 'entries' in info_search and info_search['entries']:
                video_id = info_search['entries'][0]['id']
                # Musiqani yuklash funksiyasini chaqiramiz
                await _perform_music_download(callback.message, video_id, user_id, callback.bot, state, callback, status_msg_to_use=status_msg, query_from_shazam=True)
            else:
                await callback.message.answer(get_text("not_found", lang))
                
        else:
            await status_msg.edit_text(get_text("shazam_not_found", lang))
            
    except Exception as e:
        logger.error(f"Instagram Shazam error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        DOWNLOADING_USERS.discard(user_id)
        if os.path.exists(audio_file_path): os.remove(audio_file_path)

@router.callback_query(F.data == "noop")
async def noop_callback(callback: CallbackQuery):
    """Bo'sh tugma uchun (sahifa raqami)"""
    await callback.answer()

@router.callback_query(F.data == "save_current_music")
async def save_music_callback(callback: CallbackQuery):
    if not callback.message.audio:
        await callback.answer("Xatolik: Musiqa fayli topilmadi.", show_alert=True)
        return

    user_id = callback.from_user.id
    file_id = callback.message.audio.file_id
    duration = callback.message.audio.duration
    
    caption_title = "Noma'lum musiqa"
    # Musiqa nomini aniqlash (Audio metadata -> Fayl nomi -> Caption)
    if callback.message.audio.title:
        caption_title = callback.message.audio.title
    elif callback.message.audio.file_name:
        caption_title = callback.message.audio.file_name
    elif callback.message.caption:
        temp = callback.message.caption.split('\n')[0].replace("🎵", "").replace("<b>", "").replace("</b>", "").strip()
        if temp and "@" not in temp: # Agar captionda faqat bot username bo'lmasa
            caption_title = temp

    lang = await get_user_lang(user_id)
    if await db.save_music(user_id, file_id, caption_title, duration): # noqa
        await callback.answer(get_text("music_saved_alert", lang), show_alert=True)
        builder = InlineKeyboardBuilder()
        builder.add(InlineKeyboardButton(text=get_text("music_saved", lang), callback_data="noop"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        try:
            await callback.message.edit_reply_markup(reply_markup=builder.as_markup())
        except:
            await callback.answer(get_text("music_saved_alert", lang), show_alert=True)
            pass
    else:
        await callback.answer(get_text("music_already_saved", lang), show_alert=True)

async def show_my_music(message_or_callback: Union[Message, CallbackQuery], state: FSMContext, user_id: int, lang: str, page: int = 0):
    """Saqlangan musiqalar ro'yxatini ko'rsatish uchun yordamchi funksiya"""
    message = message_or_callback if isinstance(message_or_callback, Message) else message_or_callback.message

    await state.set_state(UserStates.my_music)
    saved_music = await db.get_saved_music(user_id)
    has_deleted = await db.has_deleted_music(user_id)

    if not saved_music:
        if has_deleted:
            text = "🗑 <b>Siz barcha musiqalarni o'chirgansiz.</b>\n\nUlarni qayta tiklashni xohlaysizmi?"
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text="♻️ Tiklash", callback_data="restore_all_music"))
            builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            kb = builder.as_markup()
        else:
            text = get_text("no_saved_music", lang)
            kb = await profile_keyboard(True, lang, user_id)
        await state.clear() # Musiqa yo'q, holatni tozalaymiz
    else:
        ITEMS_PER_PAGE = 10
        total_pages = (len(saved_music) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
        start_idx = page * ITEMS_PER_PAGE
        end_idx = start_idx + ITEMS_PER_PAGE
        current_items = saved_music[start_idx:end_idx]

        # Musiqalar sonini sarlavhaga qo'shish
        text = f"{get_text('my_music_list_header_delete', lang, count=len(saved_music))}\n{get_text('page_label', lang)}: <b>{page+1}/{total_pages}</b>\n\n"
        music_list_data = [{'id': m[0], 'file_id': m[1], 'title': m[2], 'duration': m[3]} for m in saved_music]
        await state.update_data(my_music_list=music_list_data)
        
        builder = InlineKeyboardBuilder()
        
        # Qidiruv tugmasi (Eng yuqorida)
        builder.row(InlineKeyboardButton(text=get_text("search_btn", lang), callback_data="my_music_search_start"))

        # Musiqa raqamlari uchun tugmalar qatori
        btn_row = []
        for i, music in enumerate(current_items):
            display_idx = i + 1 # Sahifadagi tartib raqam (1-10)
            
            # Duration formatlash
            duration_str = ""
            if len(music) > 3 and music[3]:
                try:
                    m_dur, s_dur = divmod(int(music[3]), 60)
                    duration_str = f" <i>({m_dur:02d}:{s_dur:02d})</i>"
                except: pass
            
            text += f"<b>{display_idx}.</b> {escape(music[2])}{duration_str}\n"
            btn_row.append(InlineKeyboardButton(text=f"🎵 {display_idx}", callback_data=f"play_saved_{music[0]}"))
            
            # Har 5 ta tugmada yangi qatorga o'tish
            if len(btn_row) == 5:
                builder.row(*btn_row)
                btn_row = []
        if btn_row: builder.row(*btn_row) # Qolgan tugmalarni qo'shish

        nav_row = []
        if page > 0:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_prev_page", lang), callback_data=f"my_music_page_{page-1}"))
        

        if (page + 1) < total_pages:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_next_page", lang), callback_data=f"my_music_page_{page+1}"))
        
        builder.row(*nav_row)
        
        # Barchasini o'chirish tugmasi
        builder.row(InlineKeyboardButton(text=get_text("delete_all", lang), callback_data="delete_all_music_ask"))
        
        builder.row(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        kb = builder.as_markup()

    # Agar musiqa bo'lmasa, faqat orqaga qaytish tugmalari
    if not saved_music and not has_deleted:
        builder = InlineKeyboardBuilder()
        builder.row(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        kb = builder.as_markup()

    if isinstance(message_or_callback, CallbackQuery):
        await safe_edit_message(message_or_callback, text, reply_markup=kb)
    else:
        await message_or_callback.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data == "my_music_search_start")
async def my_music_search_start_handler(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.my_music_search)
    await callback.message.edit_text(get_text("search_music_prompt", lang), reply_markup=cancel_keyboard(lang))

@router.message(StateFilter(UserStates.my_music_search))
async def my_music_search_perform_handler(message: Message, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    query = message.text.lower().strip()
    
    saved_music = await db.get_saved_music(user_id)
    # Qidiruv (nomi bo'yicha)
    results = [m for m in saved_music if m[2] and query in m[2].lower()]
    
    if not results:
        await message.answer(get_text("not_found", lang), reply_markup=cancel_keyboard(lang))
        return

    text = f"{get_text('search_results', lang, count=len(results))}\n\n"
    builder = InlineKeyboardBuilder()
    btn_row = []
    
    for i, music in enumerate(results):
        display_idx = i + 1
        text += f"<b>{display_idx}.</b> {music[2]}\n"
        # Play tugmasi (ID orqali ishlaydi, shuning uchun muammo bo'lmaydi)
        btn_row.append(InlineKeyboardButton(text=f"🎵 {display_idx}", callback_data=f"play_saved_{music[0]}"))
        if len(btn_row) == 5:
            builder.row(*btn_row)
            btn_row = []
    if btn_row: builder.row(*btn_row)
    
    builder.row(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_my_music"))
    builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    
    await message.answer(text, parse_mode="HTML", reply_markup=builder.as_markup())

@router.callback_query(F.data == "menu_my_music")
async def my_music_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await show_my_music(callback, state, user_id, lang, page=0)

@router.callback_query(F.data.startswith("my_music_page_"))
async def my_music_pagination(callback: CallbackQuery, state: FSMContext):
    page = int(callback.data.split("_")[3])
    await show_my_music(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id), page)

# --- Videolarim bo'limi (Yangi) ---
async def show_my_videos(message_or_callback: Union[Message, CallbackQuery], state: FSMContext, user_id: int, lang: str, page: int = 0):
    message = message_or_callback if isinstance(message_or_callback, Message) else message_or_callback.message

    await state.set_state(UserStates.my_videos)
    saved_videos = await db.get_saved_videos(user_id)
    has_deleted = await db.has_deleted_videos(user_id)

    if not saved_videos:
        if has_deleted:
            text = get_text("deleted_all_videos_restore", lang)
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text=get_text("btn_restore", lang), callback_data="restore_all_videos"))
            builder.row(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
            builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            kb = builder.as_markup()
        else:
            text = get_text("no_saved_videos", lang)
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
            builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            kb = builder.as_markup()
        await state.clear()
    else:
        ITEMS_PER_PAGE = 10
        total_pages = (len(saved_videos) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
        start_idx = page * ITEMS_PER_PAGE
        end_idx = start_idx + ITEMS_PER_PAGE
        current_items = saved_videos[start_idx:end_idx]

        text = get_text("my_video_list_header_delete", lang) + "\n"
        
        builder = InlineKeyboardBuilder()
        btn_row = []
        for i, video in enumerate(current_items):
            display_idx = i + 1
            text += f"<b>{display_idx}.</b> {escape(video[2])}\n"
            btn_row.append(InlineKeyboardButton(text=str(display_idx), callback_data=f"play_saved_video_{video[0]}"))
            
            if len(btn_row) == 5:
                builder.row(*btn_row)
                btn_row = []
        if btn_row: builder.row(*btn_row)

        nav_row = []
        if page > 0:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_prev_page", lang), callback_data=f"my_videos_page_{page-1}"))
        if (page + 1) < total_pages:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_next_page", lang), callback_data=f"my_videos_page_{page+1}"))
        builder.row(*nav_row)
        
        builder.row(InlineKeyboardButton(text=get_text("delete_all", lang), callback_data="delete_all_videos_ask"))
        builder.row(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        kb = builder.as_markup()

    if isinstance(message_or_callback, CallbackQuery):
        await safe_edit_message(message_or_callback, text, reply_markup=kb)
    else:
        await message_or_callback.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data == "save_current_video")
async def save_video_callback(callback: CallbackQuery, state: FSMContext):
    """Videoni saqlash tugmasi bosilganda ishlaydi"""
    msg = callback.message

    # Video yoki Video Note ekanligini tekshiramiz
    file_id = msg.video.file_id if msg.video else (
        msg.video_note.file_id if msg.video_note else None
    )

    if not file_id:
        await callback.answer("Xatolik: Video fayli topilmadi.", show_alert=True)
        return

    user_id = callback.from_user.id
    caption = msg.caption or "Video"

    # Captiondan ortiqcha narsalarni tozalash
    clean_caption = caption.split("\n")[0] \
        .replace("📹", "") \
        .replace("<b>", "") \
        .replace("</b>", "") \
        .strip()

    lang = await get_user_lang(user_id)

    if await db.save_video(user_id, file_id, clean_caption):
        await callback.answer(get_text("video_saved_alert", lang), show_alert=True)
    else:
        await callback.answer(get_text("video_already_saved", lang), show_alert=True)

@router.callback_query(F.data == "save_current_image")
async def save_image_callback(callback: CallbackQuery, state: FSMContext):
    """Rasmni saqlash tugmasi bosilganda ishlaydi"""
    msg = callback.message
    
    # Rasm yoki hujjat ekanligini tekshiramiz
    file_id = msg.photo[-1].file_id if msg.photo else (msg.document.file_id if msg.document else None)

    if not file_id:
        await callback.answer("Xatolik: Rasm fayli topilmadi.", show_alert=True)
        return

    user_id = callback.from_user.id
    caption = msg.caption or "Rasm"
    clean_caption = caption.split("\n")[0].strip()
    lang = await get_user_lang(user_id)

    if await db.save_image(user_id, file_id, clean_caption):
        await callback.answer(get_text("image_saved_alert", lang), show_alert=True)
    else:
        await callback.answer(get_text("image_already_saved", lang), show_alert=True)

@router.callback_query(F.data == "menu_my_videos")
async def my_videos_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await show_my_videos(callback, state, user_id, lang, page=0)

@router.callback_query(F.data.startswith("my_videos_page_"))
async def my_videos_pagination(callback: CallbackQuery, state: FSMContext):
    page = int(callback.data.split("_")[3])
    await show_my_videos(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id), page)

@router.callback_query(lambda c: c.data.startswith("play_saved_video_"))
async def play_saved_video_callback(callback: CallbackQuery):
    video_db_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    
    saved_videos = await db.get_saved_videos(user_id)
    target_video = next((v for v in saved_videos if v[0] == video_db_id), None)
    
    if target_video:
        file_id = target_video[1]
        caption = target_video[2]

        # Videoni yuborishda "bot orqali yuklandi" so'zini qo'shish (mavjud va yangi videolar uchun)
        bot_username = (await callback.bot.get_me()).username
        attribution = get_text('downloaded_via_bot', lang, bot_username=bot_username)
        if attribution not in caption:
            caption = f"{caption}\n\n{attribution}"
        
        del_kb = InlineKeyboardBuilder()
        del_kb.add(InlineKeyboardButton(text="🗑️ O'chirish", callback_data=f"del_video_btn_{video_db_id}"))
        del_kb.add(InlineKeyboardButton(text="✏️ Tahrirlash", callback_data=f"edit_video_caption_{video_db_id}"))
        del_kb.add(InlineKeyboardButton(text=get_text("back_to_video", lang), callback_data="menu_video"))
        del_kb.adjust(1)
        
        await callback.message.answer_video(file_id, caption=caption, parse_mode="HTML", reply_markup=del_kb.as_markup())
        await callback.answer()
    else:
        await callback.answer("Video topilmadi yoki o'chirilgan.", show_alert=True)

@router.callback_query(lambda c: c.data.startswith("del_video_btn_"))
async def delete_video_btn_callback(callback: CallbackQuery):
    video_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    if await db.delete_saved_video(video_id, user_id):
        await callback.answer("Video o'chirildi! 🗑️")
        await callback.message.delete()
    else:
        await callback.answer("Xatolik.", show_alert=True)

# --- Videoni Tahrirlash Handlerlari ---
@router.callback_query(F.data.startswith("edit_video_caption_"))
async def edit_video_caption_callback(callback: CallbackQuery, state: FSMContext):
    video_id = int(callback.data.split("_")[3])
    await state.update_data(edit_video_id=video_id)
    await state.set_state(UserStates.edit_video_caption)
    await callback.message.reply("Videoga yangi nom bering: ✏️", reply_markup=cancel_keyboard(await get_user_lang(callback.from_user.id)))
    await callback.answer()

@router.message(StateFilter(UserStates.edit_video_caption))
async def save_video_caption_handler(message: Message, state: FSMContext):
    data = await state.get_data()
    video_id = data.get("edit_video_id")
    new_caption = message.text
    user_id = message.from_user.id
    
    if await db.update_video_caption(video_id, user_id, new_caption):
        await message.answer("Nom yangilandi! ✅")
        await show_my_videos(message, state, user_id, await get_user_lang(user_id))
    else:
        await message.answer("Xatolik yuz berdi.")
    await state.clear()

# --- Rasmlarim Bo'limi (Yangi) ---
@router.callback_query(F.data == "menu_my_images")
async def my_images_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await show_my_images(callback, state, user_id, lang, page=0)

async def show_my_images(message_or_callback: Union[Message, CallbackQuery], state: FSMContext, user_id: int, lang: str, page: int = 0):
    message = message_or_callback if isinstance(message_or_callback, Message) else message_or_callback.message

    await state.set_state(UserStates.my_images)
    saved_images = await db.get_saved_images(user_id)
    has_deleted = await db.has_deleted_images(user_id)

    if not saved_images:
        text = get_text("no_saved_images", lang)
        builder = InlineKeyboardBuilder()
        builder.add(InlineKeyboardButton(text=get_text("back_to_images", lang), callback_data="menu_image"))
        builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        kb = builder.as_markup()
        await state.clear()
    else:
        ITEMS_PER_PAGE = 10
        total_pages = (len(saved_images) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
        start_idx = page * ITEMS_PER_PAGE
        end_idx = start_idx + ITEMS_PER_PAGE
        current_items = saved_images[start_idx:end_idx]

        text = f"{get_text('my_images_list_header', lang)}\n{get_text('page_label', lang)}: <b>{page+1}/{total_pages}</b>\n\n"
        
        builder = InlineKeyboardBuilder()
        btn_row = []
        for i, img in enumerate(current_items):
            display_idx = i + 1
            text += f"<b>{display_idx}.</b> {escape(img[2])}\n"
            btn_row.append(InlineKeyboardButton(text=str(display_idx), callback_data=f"play_saved_image_{img[0]}"))
            
            if len(btn_row) == 5:
                builder.row(*btn_row)
                btn_row = []
        if btn_row: builder.row(*btn_row)

        nav_row = []
        if page > 0:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_prev_page", lang), callback_data=f"my_images_page_{page-1}"))
        if (page + 1) < total_pages:
            nav_row.append(InlineKeyboardButton(text=get_text("btn_next_page", lang), callback_data=f"my_images_page_{page+1}"))
        builder.row(*nav_row)
        
        builder.row(InlineKeyboardButton(text=get_text("back_to_images", lang), callback_data="menu_image"))
        builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        kb = builder.as_markup()

    if isinstance(message_or_callback, CallbackQuery):
        await safe_edit_message(message_or_callback, text, reply_markup=kb)
    else:
        await message_or_callback.answer(text, parse_mode="HTML", reply_markup=kb)

@router.callback_query(F.data.startswith("my_images_page_"))
async def my_images_pagination(callback: CallbackQuery, state: FSMContext):
    page = int(callback.data.split("_")[3])
    await show_my_images(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id), page)

@router.callback_query(lambda c: c.data.startswith("play_saved_image_"))
async def play_saved_image_callback(callback: CallbackQuery):
    image_db_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    
    saved_images = await db.get_saved_images(user_id)
    target_image = next((v for v in saved_images if v[0] == image_db_id), None)
    
    if target_image:
        file_id = target_image[1]
        caption = target_image[2]
        
        del_kb = InlineKeyboardBuilder()
        del_kb.add(InlineKeyboardButton(text="🗑️ O'chirish", callback_data=f"del_image_btn_{image_db_id}"))
        del_kb.add(InlineKeyboardButton(text=get_text("back_to_images", lang), callback_data="menu_image"))
        del_kb.adjust(1)
        
        try:
            await callback.message.answer_photo(file_id, caption=caption, parse_mode="HTML", reply_markup=del_kb.as_markup())
        except TelegramBadRequest:
            # Agar rasm sifatida yuborib bo'lmasa (Document bo'lsa), Document sifatida yuboramiz
            await callback.message.answer_document(file_id, caption=caption, parse_mode="HTML", reply_markup=del_kb.as_markup())
        await callback.answer()
    else:
        await callback.answer("Rasm topilmadi.", show_alert=True)

@router.callback_query(lambda c: c.data.startswith("del_image_btn_"))
async def delete_image_btn_callback(callback: CallbackQuery):
    image_id = int(callback.data.split("_")[3])
    user_id = callback.from_user.id
    if await db.delete_saved_image(image_id, user_id):
        await callback.answer("Rasm o'chirildi! 🗑️")
        await callback.message.delete()
    else:
        await callback.answer("Xatolik.", show_alert=True)

# --- Musiqalarni o'chirish va tiklash handlerlari ---
@router.callback_query(F.data == "delete_all_music_ask")
async def delete_all_music_ask(callback: CallbackQuery):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", await get_user_lang(callback.from_user.id)), callback_data="confirm_delete_music_yes"))
    builder.add(InlineKeyboardButton(text=get_text("no", await get_user_lang(callback.from_user.id)), callback_data="confirm_delete_music_no"))
    await callback.message.edit_text("⚠️ <b>Diqqat!</b>\n\nRostdan ham barcha saqlangan musiqalarni o'chirmoqchimisiz?", parse_mode="HTML", reply_markup=builder.as_markup())

@router.callback_query(F.data == "confirm_delete_music_yes")
async def confirm_delete_music_yes(callback: CallbackQuery, state: FSMContext):
    await db.soft_delete_all_music(callback.from_user.id)
    await callback.answer("Barcha musiqalar o'chirildi! 🗑")
    await show_my_music(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id))

@router.callback_query(F.data == "confirm_delete_music_no")
async def confirm_delete_music_no(callback: CallbackQuery, state: FSMContext):
    await callback.answer("Bekor qilindi.")
    await show_my_music(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id))

@router.callback_query(F.data == "restore_all_music")
async def restore_all_music(callback: CallbackQuery, state: FSMContext):
    await db.restore_all_music(callback.from_user.id)
    await callback.answer("Musiqalar tiklandi! ✅")
    await show_my_music(callback, state, callback.from_user.id, await get_user_lang(callback.from_user.id))

# --- Videolarni o'chirish va tiklash handlerlari ---
@router.callback_query(F.data == "delete_all_videos_ask")
async def delete_all_videos_ask(callback: CallbackQuery):
    lang = await get_user_lang(callback.from_user.id)
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", lang), callback_data="confirm_delete_videos_yes"))
    builder.add(InlineKeyboardButton(text=get_text("no", lang), callback_data="confirm_delete_videos_no"))
    await callback.message.edit_text(get_text("confirm_delete_all_videos", lang), parse_mode="HTML", reply_markup=builder.as_markup())

@router.callback_query(F.data == "confirm_delete_videos_yes")
async def confirm_delete_videos_yes(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await db.soft_delete_all_videos(callback.from_user.id)
    await show_my_videos(callback, state, callback.from_user.id, lang)

@router.callback_query(F.data == "confirm_delete_videos_no")
async def confirm_delete_videos_no(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await callback.answer(get_text("cancelled_text", lang))
    await show_my_videos(callback, state, callback.from_user.id, lang)

@router.callback_query(F.data == "restore_all_videos")
async def restore_all_videos(callback: CallbackQuery, state: FSMContext):
    lang = await get_user_lang(callback.from_user.id)
    await db.restore_all_videos(callback.from_user.id)
    await callback.answer(get_text("all_restored", lang))
    await show_my_videos(callback, state, callback.from_user.id, lang)

# --- Yangi Handler: Saqlangan musiqani tugma orqali ijro etish ---
@router.callback_query(lambda c: c.data.startswith("play_saved_") and not c.data.startswith("play_saved_video_"))
async def play_saved_music_callback(callback: CallbackQuery):
    music_db_id = int(callback.data.split("_")[2])
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    
    # Bazadan faylni olish
    saved_music = await db.get_saved_music(user_id)
    target_music = next((m for m in saved_music if m[0] == music_db_id), None)
    
    if target_music:
        file_id = target_music[1]
        title = target_music[2]
        bot_username = (await callback.bot.get_me()).username
        caption = get_text("saved_via_bot", lang, title=title, bot_username=bot_username)
        
        # O'chirish va tahrirlash tugmalari bilan yuborish
        del_kb = InlineKeyboardBuilder()
        del_kb.add(InlineKeyboardButton(text="✏️ Nomini o'zgartirish", callback_data=f"edit_music_btn_{music_db_id}"))
        del_kb.add(InlineKeyboardButton(text="🗑️ O'chirish", callback_data=f"del_music_btn_{music_db_id}"))
        del_kb.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
        del_kb.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
        del_kb.adjust(1) # Vertikal tugmalar
        
        await callback.message.answer_audio(file_id, caption=caption, title=title, parse_mode="HTML", reply_markup=del_kb.as_markup())
        await callback.answer()
    else:
        await callback.answer("Musiqa topilmadi yoki o'chirilgan.", show_alert=True)

@router.callback_query(F.data.startswith("dl_music_"))
async def download_music_callback(callback: CallbackQuery, state: FSMContext):
    video_id = callback.data[9:] # "dl_music_" (9 ta belgi) dan keyingi hammasini olish
    user_id = callback.from_user.id
    await _perform_music_download(callback.message, video_id, user_id, callback.bot, state, callback, status_msg_to_use=None)

async def _perform_music_download(message: Message, video_id: str, user_id: int, bot: Bot, state: FSMContext, callback: Optional[CallbackQuery] = None, status_msg_to_use: Optional[Message] = None, query_from_shazam: bool = False):
    """Musiqa yuklash logikasi (Callback va Message uchun umumiy)"""
    # Guruh yoki shaxsiy chat ekanligini aniqlash (target_chat_id)
    target_chat_id = message.chat.id if message else (callback.message.chat.id if callback else user_id)

    lang = await get_user_lang(user_id)
    is_admin = user_id in ADMIN_IDS
    if user_id in DOWNLOADING_USERS:
        if callback:
            await callback.answer(get_text("download_in_progress_alert", lang), show_alert=True)
        # Message holatida jim turamiz (return)
        return

    if callback:
        await callback.answer()
    # Server yuklamasini tekshirish
    if download_semaphore.locked():
        if callback: await callback.answer("⚠️ Server yuklama bilan band. Iltimos, biroz kuting.", show_alert=True)
        else: await message.answer("⚠️ Server yuklama bilan band. Iltimos, biroz kuting.")
        return

    status_msg = status_msg_to_use
    if not status_msg:
        cached_file = await db.get_cached_media(video_id, quality="mp3")
        if cached_file:
            file_id, _, cached_title = cached_file
            title_to_use = cached_title if cached_title else get_text("music", lang)
            bot_username = (await bot.get_me()).username
            caption = get_text("saved_via_bot", lang, title=title_to_use, bot_username=bot_username)
            
            # Foydalanuvchida saqlanganligini tekshirish
            saved_music_list = await db.get_saved_music(user_id)
            is_already_saved = any(m[1] == file_id for m in saved_music_list)
            
            save_kb_builder = InlineKeyboardBuilder()
            if is_already_saved:
                save_kb_builder.add(InlineKeyboardButton(text=get_text("music_already_saved", lang), callback_data="noop"))
            else:
                save_kb_builder.add(InlineKeyboardButton(text=get_text("save_music", lang), callback_data="save_current_music"))
            
            save_kb_builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
            save_kb_builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            save_kb_builder.adjust(1)
            
            await message.answer_audio(file_id, caption=caption, parse_mode="HTML", reply_markup=save_kb_builder.as_markup())
            if callback: await callback.answer()
            return
        status_msg = await message.answer(get_text("searching_music", lang), parse_mode="HTML")

        # Sharh: Musiqani qayta yuklashdan oldin, uning nomini olib, foydalanuvchining saqlangan musiqalari orasidan qidiramiz.
        # Bu vaqtni va trafikni tejaydi.
        try:
            # 1. Avval videoning ma'lumotlarini (nomini) yuklab olamiz
            temp_ydl_opts = {'quiet': True, 'skip_download': True, 'source_address': '0.0.0.0'}
            with yt_dlp.YoutubeDL(temp_ydl_opts) as ydl:
                info = ydl.extract_info(f"https://www.youtube.com/watch?v={video_id}", download=False)
                video_title = info.get('title')

            # 2. Agar nomini olsagu, saqlanganlar orasidan tekshiramiz
            if video_title:
                saved_music = await db.get_saved_music(user_id)
                for saved_item in saved_music:
                    saved_title = saved_item[2]
                    # Oddiy, registrdan qat'iy nazar taqqoslash
                    if saved_title and video_title.strip().lower() == saved_title.strip().lower():
                        await status_msg.edit_text("✅ Musiqa saqlanganlar orasidan topildi!")
                        
                        file_id = saved_item[1]
                        bot_username = (await bot.get_me()).username
                        caption = get_text("saved_via_bot", lang, title=saved_title, bot_username=bot_username)
                        
                        save_kb_builder = InlineKeyboardBuilder()
                        save_kb_builder.add(InlineKeyboardButton(text=get_text("music_already_saved", lang), callback_data="noop"))
                        save_kb_builder.row(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
                        save_kb_builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))

                        await message.answer_audio(
                            file_id, caption=caption, title=saved_title, parse_mode="HTML",
                            reply_markup=save_kb_builder.as_markup()
                        )
                        await status_msg.delete()
                        return # Qayta yuklashni oldini olish uchun funksiyadan chiqamiz
        except Exception as e:
            logger.warning(f"Saqlangan musiqani tekshirishda xato (baribir yuklab ko'ramiz): {e}")

        await status_msg.edit_text(get_text("music_download_wait", lang), parse_mode="HTML")

    os.makedirs("downloads", exist_ok=True)
    DOWNLOADING_USERS.add(user_id)

    # 🚀 Optimallashtirish: cookies bilan YouTube autentifikatsiyasini saqlab qolish
    auth_sources_to_try = youtube_auth_sources()
    clients_to_try = YOUTUBE_PLAYER_CLIENTS
    # Format fallback zanjiri - eng yumshoq dan eng qat'iyga
    format_options = [
        "bestaudio/best",  # Prioritize m4a (better compatibility)
        "bestaudio/best",
        "best[ext=mp4]/best",
        "best",
    ]
    last_exception = None
    success = False
    filename = None
    title = None

    for auth_source in auth_sources_to_try:
        if success:
            break
        
        for fmt_option in format_options:
            if success:
                break
            for client in clients_to_try:
                if success: break
                try:
                    loop = asyncio.get_event_loop()

                    unique_out_name = f"music_{video_id}_{int(time.time())}"
                    
                    last_update_time = [time.time()]
                    hook = partial(progress_hook, bot=bot, message=status_msg, last_update_time=last_update_time, loop=loop, lang=lang, finished_text_key="music_almost_ready")
                    
                    # Issue 16: Broken yt-dlp Format String - Fixed by using fmt_option directly
                    # and ensuring postprocessors are correctly applied for MP3.
                    ydl_opts = {
                        "format": fmt_option,
                        "noplaylist": True,
                        "quiet": True,
                        "ignoreerrors": True,
                        "outtmpl": f"downloads/{unique_out_name}.%(ext)s",
                        "postprocessors": [{"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}],
                        "geo_bypass": True,
                        "socket_timeout": 60,
                        'extractor_args': {'youtube': {
                            'player_client': YOUTUBE_PLAYER_CLIENTS,
                            'remote_components': True
                        }},
                        'progress_hooks': [hook],
                        'nocheckcertificate': True,
                    }
                    apply_youtube_auth(ydl_opts, auth_source)
                    source_type, source_value = auth_source
                    logger.info("Yuklash: Auth=%s, Format=%s, Client=%s", os.path.basename(source_value) if source_type == "file" else source_value or "cookiesiz", fmt_option, client)

                    url = f"https://www.youtube.com/watch?v={video_id}"

                    # Semafor bilan o'rash (serverni himoya qilish)
                    async with download_semaphore:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            # Timeout qo'shish (qotib qolmasligi uchun)
                            info = await asyncio.wait_for(
                                loop.run_in_executor(None, lambda: ydl.extract_info(url, download=True)),
                                timeout=180.0
                            )

                            if info:
                                filesize = info.get('filesize') or info.get('filesize_approx') or 0
                                filename = clean_path(f"downloads/{unique_out_name}.mp3")
                                title = info.get('title', 'Music')
                            else:
                                filename = None
                                title = None

                    if filename and os.path.exists(filename):
                        bot_username = (await bot.get_me()).username
                        saved_music_list = await db.get_saved_music(user_id)
                        is_already_saved = any(m[1] == info.get('id') for m in saved_music_list) # Check if file_id is already saved

                        # Captionni tarjimadan olish
                        caption = get_text("downloaded_via_bot", lang, bot_username=bot_username)

                        save_kb_builder = InlineKeyboardBuilder()
                        if is_already_saved:
                            save_kb_builder.add(InlineKeyboardButton(text=get_text("music_already_saved", lang), callback_data="noop"))
                        else:
                            save_kb_builder.add(InlineKeyboardButton(text=get_text("save_music", lang), callback_data="save_current_music"))
                        save_kb_builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
                        save_kb_builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
                        save_kb_builder.adjust(1)

                        # Katta fayllarni ham yuborish uchun `smart_send_audio` dan foydalanish
                        sent_msg = await smart_send_audio(
                            bot=bot,
                            chat_id=target_chat_id, # User ID emas, Target Chat ID (Guruh/Lichka)
                            file_path=filename,
                            caption=caption,
                            title=title, # Musiqa nomi fayl ichida bo'ladi
                            performer=info.get('artist') or info.get('uploader') or "Unknown", # Ijrochi
                            duration=info.get('duration'),
                            reply_markup=save_kb_builder.as_markup()
                        )

                        if not sent_msg or not getattr(sent_msg, 'audio', None):
                            raise Exception("Audio fayli yuborilmadi. Userbot yoki kichikroq fayl kerak.")

                        await status_msg.delete()
                        await safe_remove(filename)
                        await db.add_download_stat(user_id, "music")
                        # Keshga saqlash
                        await db.save_cached_media(video_id, sent_msg.audio.file_id, "audio", "mp3", filesize, title=title)
                        success = True
                    else:
                        logger.warning(f"Fayl yuklandi lekin {filename} topilmadi. Cookie yoki format xatosi bo'lishi mumkin.")
                        last_exception = Exception("Fayl yuklangandan so'ng topilmadi.")
                        continue

                except asyncio.TimeoutError:
                    last_exception = Exception("Yuklash vaqti tugadi (Timeout). Server band bo'lishi mumkin.")
                    continue  # Try next format option
                except DownloadError as e:
                    last_exception = e
                    if "Sign in to confirm" in str(e) or "authentication" in str(e):
                        logger.warning("Cookie bilan autentifikatsiya xatosi (%s). Keyingisi sinab ko'riladi.", auth_source)
                        continue # Try next cookie
                    elif "Requested format is not available" in str(e):
                        logger.warning(f"Format mavjud emas ({fmt_option}). Keyingi format sinab ko'riladi.")
                        continue # Try next format
                    else:
                        logger.warning(f"❌ YouTube download xatosi: {str(e)}. Keyingi format sinab ko'riladi.")
                        continue # Try next format
                except Exception as e:
                    logger.error(f"❌ Kutilmagan xato (Music): {str(e)}")
                    last_exception = e
                    continue

    if not success and last_exception:
        logger.error(f"Music download error (yt-dlp): {last_exception}", exc_info=True)
        # Foydalanuvchiga texnik xatoni ko'rsatmaymiz, faqat chiroyli xabar
        error_text = get_text('music_download_error_external', lang)
        try:
            await status_msg.edit_text(error_text, parse_mode="HTML")
        except:
            if not callback: await message.answer(error_text, parse_mode="HTML")
        
        if callback:
            try:
                await callback.answer(error_text, show_alert=True)
            except TelegramBadRequest:
                pass # Callback eskirgan bo'lsa, e'tibor bermaymiz

    DOWNLOADING_USERS.discard(user_id)

@router.callback_query(F.data.startswith("del_music_btn_"))
async def delete_music_btn_callback(callback: CallbackQuery):
    try:
        music_id = int(callback.data.split("_")[3])
        user_id = callback.from_user.id
        
        if await db.delete_saved_music(music_id, user_id):
            await callback.answer("Musiqa o'chirildi! 🗑️")
            try:
                await callback.message.delete()
            except:
                pass  # Xabar allaqachon o'chirilgan bo'lsa, error bermaymiz
        else:
            await callback.answer("Xatolik yoki musiqa allaqachon o'chirilgan.", show_alert=True)
    except (ValueError, IndexError) as e:
        logger.error(f"Delete music button error: {e}")
        await callback.answer("Xatolik yuz berdi. Qayta urinib ko'ring.", show_alert=True)

@router.callback_query(F.data.startswith("edit_music_btn_"))
async def edit_music_btn_callback(callback: CallbackQuery, state: FSMContext):
    try:
        music_id = int(callback.data.split("_")[3])
        user_id = callback.from_user.id
        lang = await get_user_lang(user_id)
        
        # Musiqaning hozirgi nomini olish
        saved_music = await db.get_saved_music(user_id)
        target_music = next((m for m in saved_music if m[0] == music_id), None)
        
        if target_music:
            current_title = target_music[2]
            await state.update_data(edit_music_id=music_id, current_music_title=current_title)
            await state.set_state(UserStates.edit_music)
            
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text=get_text("back_to_music", lang), callback_data="menu_music"))
            builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
            builder.adjust(1)
            
            # Audio xabarini o'chirib, yangi text xabar yuborish
            try:
                await callback.message.delete()
            except:
                pass
            
            await callback.message.answer(
                f"🎵 <b>Yangi nom bering:</b>\n\n<i>Hozirgi nom:</i> {escape(current_title)}",
                parse_mode="HTML",
                reply_markup=builder.as_markup()
            )
            await callback.answer()
        else:
            await callback.answer("Musiqa topilmadi yoki o'chirilgan.", show_alert=True)
    except (ValueError, IndexError) as e:
        logger.error(f"Edit music button error: {e}")
        await callback.answer("Xatolik yuz berdi. Qayta urinib ko'ring.", show_alert=True)

@router.message(StateFilter(UserStates.edit_music))
async def edit_music_title_handler(message: Message, state: FSMContext):
    try:
        user_id = message.from_user.id
        lang = await get_user_lang(user_id)
        data = await state.get_data()
        music_id = data.get("edit_music_id")
        
        new_title = message.text.strip()
        
        if len(new_title) > 100:
            await message.answer("❌ Nom 100 ta belgidan oshmasligi kerak!")
            return
        
        if len(new_title) < 1:
            await message.answer("❌ Nom bo'sh bo'lmasligi kerak!")
            return
        
        if await db.update_music_title(music_id, user_id, new_title):
            await message.answer(f"✅ Musiqa nomi muvaffaqiyatli o'zgartirildi!\n\n🎵 <b>Yangi nom:</b> {escape(new_title)}", parse_mode="HTML")
            await state.clear()
            # Orqaga qaytish
            await show_my_music(message, state, user_id, lang)
        else:
            await message.answer("❌ Nomni o'zgartirishda xato yuz berdi. Qayta urinib ko'ring.")
    except Exception as e:
        logger.error(f"Edit music title error: {e}")
        await message.answer("❌ Xatolik yuz berdi. Qayta urinib ko'ring.")

        

# ============================================================
# YUKLASH UCHUN YORDAMCHI FUNKSIYALAR (YANGI)
# ============================================================



class _ScriptCollector(HTMLParser):
    def __init__(self):
        super().__init__()
        self.in_script = False
        self.current = []
        self.scripts = []
    def handle_starttag(self, tag, attrs):
        if tag.lower() == "script":
            self.in_script = True
            self.current = []
    def handle_endtag(self, tag):
        if tag.lower() == "script" and self.in_script:
            self.scripts.append("".join(self.current))
            self.in_script = False
    def handle_data(self, data):
        if self.in_script:
            self.current.append(data)


def _balanced_json_value(text: str, start: int):
    """start nuqtasidan { yoki [ bilan boshlangan JSON qiymatni ajratadi."""
    if start < 0 or start >= len(text) or text[start] not in "[{":
        return None
    opening = text[start]
    closing = "]" if opening == "[" else "}"
    depth = 0
    in_string = False
    escaped = False
    for i in range(start, len(text)):
        ch = text[i]
        if in_string:
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
        elif ch == opening:
            depth += 1
        elif ch == closing:
            depth -= 1
            if depth == 0:
                return text[start:i + 1]
    return None


def _collect_instagram_media_objects(obj, out):
    """Instagram JSON ichidan faqat media-ga o'xshash obyektlarni yig'adi."""
    if isinstance(obj, dict):
        # Reel/video media
        for key in ("video_versions", "video_url"):
            if key in obj:
                out.append(obj)
                break
        # Photo media
        if "image_versions2" in obj or "display_url" in obj:
            out.append(obj)
        for value in obj.values():
            if isinstance(value, (dict, list)):
                _collect_instagram_media_objects(value, out)
    elif isinstance(obj, list):
        for value in obj:
            if isinstance(value, (dict, list)):
                _collect_instagram_media_objects(value, out)


def _instagram_media_urls_from_html(html: str):
    """Instagram sahifa HTML/JSONidan carousel/story/post media URLlarini ajratadi."""
    parser = _ScriptCollector()
    try:
        parser.feed(html)
    except Exception:
        pass

    objects = []
    scripts = parser.scripts or [html]
    for script in scripts:
        # JSON-LD va eski sharedData uchun to'g'ridan-to'g'ri JSON urinishlari.
        stripped = script.strip()
        candidates = []
        if stripped.startswith("{") or stripped.startswith("["):
            candidates.append(stripped)
        for marker in ("window._sharedData =", "__additionalDataLoaded(", "window.__additionalDataLoaded("):
            idx = script.find(marker)
            if idx >= 0:
                brace = script.find("{", idx)
                bracket = script.find("[", idx)
                starts = [x for x in (brace, bracket) if x >= 0]
                if starts:
                    raw = _balanced_json_value(script, min(starts))
                    if raw:
                        candidates.append(raw)
        # Zamonaviy inline data: carousel_media / items obyektlarini balanced parser bilan olamiz.
        for key in ('"carousel_media"', '"items"', '"media"'):
            seek = 0
            while True:
                idx = script.find(key, seek)
                if idx < 0:
                    break
                colon = script.find(":", idx + len(key))
                if colon >= 0:
                    brace = script.find("{", colon + 1)
                    bracket = script.find("[", colon + 1)
                    starts = [x for x in (brace, bracket) if x >= 0 and x < colon + 200]
                    if starts:
                        raw = _balanced_json_value(script, min(starts))
                        if raw:
                            candidates.append(raw)
                seek = idx + len(key)

        for raw in candidates:
            try:
                parsed = json.loads(raw)
                _collect_instagram_media_objects(parsed, objects)
            except Exception:
                continue

    # Oxirgi fallback: sahifada ko'rinadigan media URL kalitlari.
    media_pairs = []
    for m in re.finditer(r'"(display_url|video_url)"\s*:\s*"((?:\\.|[^"\\])+)"', html):
        try:
            media_pairs.append((m.group(1), json.loads('"' + m.group(2) + '"')))
        except Exception:
            pass

    urls = []
    seen = set()
    def add(kind, value):
        if not value or not isinstance(value, str):
            return
        value = value.replace("\\/", "/").replace("\\u0026", "&")
        if not value.startswith(("http://", "https://")):
            return
        low = value.lower()
        # Profil/avatar va ikonlarni o'tkazib yuborish.
        if any(x in low for x in ("/profile_pic", "s150x150", "s320x320", "s640x640")):
            return
        key = value.split("?")[0]
        if key in seen:
            return
        seen.add(key)
        ext = os.path.splitext(urllib.parse.urlparse(value).path)[1].lower()
        if kind == "video" or ext in (".mp4", ".m4v", ".mov", ".webm"):
            urls.append(("video", value))
        else:
            urls.append(("image", value))

    # Strukturali obyektlar afzal.
    for obj in objects:
        if not isinstance(obj, dict):
            continue
        vlist = obj.get("video_versions")
        if isinstance(vlist, list):
            for v in vlist:
                if isinstance(v, dict):
                    add("video", v.get("url"))
        add("video", obj.get("video_url"))
        iv = obj.get("image_versions2")
        if isinstance(iv, dict):
            cands = iv.get("candidates")
            if isinstance(cands, list):
                # Eng katta rasmni keyinroq tanlash uchun barcha candidate'larni yig'amiz.
                for c in sorted((x for x in cands if isinstance(x, dict)), key=lambda x: x.get("width", 0) or 0, reverse=True):
                    add("image", c.get("url"))
        add("image", obj.get("display_url"))

    for kind, value in media_pairs:
        add(kind, value)

    return urls


def _instagram_web_media_download_sync(url: str, auth_source, out_dir: str, prefix: str):
    """yt-dlp cookie sessiyasi orqali Instagram HTMLdan media URLlarini olib yuklaydi."""
    opts = {
        "quiet": True,
        "no_warnings": True,
        "nocheckcertificate": True,
        "socket_timeout": 30,
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/131.0.0.0 Safari/537.36",
            "Accept-Language": "en-US,en;q=0.9",
        },
    }
    apply_browser_auth(opts, auth_source)
    with yt_dlp.YoutubeDL(opts) as ydl:
        response = ydl.urlopen(url)
        raw = response.read()
        html = raw.decode("utf-8", "ignore")
    media_urls = _instagram_media_urls_from_html(html)
    # Dublikatlarni olib tashlab, bitta rasmning turli candidate URLlarini takrorlamaymiz.
    final = []
    seen = set()
    for kind, media_url in media_urls:
        base = media_url.split("?")[0]
        if base in seen:
            continue
        seen.add(base)
        final.append((kind, media_url))
    downloaded = []
    headers = {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/131.0.0.0 Safari/537.36",
        "Referer": "https://www.instagram.com/",
    }
    for index, (kind, media_url) in enumerate(final, 1):
        ext = ".mp4" if kind == "video" else os.path.splitext(urllib.parse.urlparse(media_url).path)[1].lower()
        if ext not in {".mp4", ".m4v", ".mov", ".webm", ".jpg", ".jpeg", ".png", ".webp", ".gif"}:
            ext = ".mp4" if kind == "video" else ".jpg"
        path = os.path.join(out_dir, f"{prefix}_web_{index:02d}{ext}")
        req = urllib.request.Request(media_url, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=60) as resp, open(path, "wb") as f:
                while True:
                    chunk = resp.read(1024 * 1024)
                    if not chunk:
                        break
                    f.write(chunk)
            if os.path.isfile(path) and os.path.getsize(path) > 0:
                downloaded.append(path)
            else:
                try: os.remove(path)
                except OSError: pass
        except Exception:
            try: os.remove(path)
            except OSError: pass
    return downloaded

async def probe_video_metadata(file_path: str):
    """Tayyor video o'lchami va davomiyligini ffprobe orqali aniq oladi."""
    try:
        process = await asyncio.create_subprocess_exec(
            "ffprobe", "-v", "error",
            "-select_streams", "v:0",
            "-show_entries", "stream=width,height,duration",
            "-of", "json", file_path,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.DEVNULL,
        )
        stdout, _ = await process.communicate()
        if process.returncode != 0:
            return None, None, None
        data = json.loads(stdout.decode("utf-8", "ignore") or "{}")
        stream = (data.get("streams") or [{}])[0]
        width = int(stream.get("width")) if stream.get("width") else None
        height = int(stream.get("height")) if stream.get("height") else None
        duration = int(float(stream.get("duration"))) if stream.get("duration") else None
        return width, height, duration
    except Exception:
        return None, None, None

async def ensure_telegram_compatible_video(input_path: str) -> str:
    """Videoni imkon qadar tez tayyorlaydi: mos H.264/AAC bo'lsa qayta encode qilmaydi."""
    if not os.path.isfile(input_path):
        raise FileNotFoundError(input_path)

    probe_cmd = [
        "ffprobe", "-v", "error", "-select_streams", "v:0",
        "-show_entries", "stream=codec_name,pix_fmt,profile,level",
        "-of", "json", input_path,
    ]
    audio_cmd = [
        "ffprobe", "-v", "error", "-select_streams", "a:0",
        "-show_entries", "stream=codec_name", "-of", "json", input_path,
    ]
    try:
        vp = await asyncio.create_subprocess_exec(*probe_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
        ap = await asyncio.create_subprocess_exec(*audio_cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
        vout, _ = await vp.communicate()
        aout, _ = await ap.communicate()
        vd = json.loads(vout.decode("utf-8", "ignore") or "{}")
        ad = json.loads(aout.decode("utf-8", "ignore") or "{}")
        vs = (vd.get("streams") or [{}])[0]
        ass = (ad.get("streams") or [{}])[0]
        vcodec = (vs.get("codec_name") or "").lower()
        acodec = (ass.get("codec_name") or "").lower()
        pix_fmt = (vs.get("pix_fmt") or "").lower()
        level = int(vs.get("level") or 0)
        compatible = vcodec == "h264" and pix_fmt == "yuv420p" and level <= 51 and (not acodec or acodec == "aac")
    except Exception:
        compatible = False

    output_path = os.path.splitext(input_path)[0] + "_compatible.mp4"
    if compatible and os.path.splitext(input_path)[1].lower() == ".mp4":
        # stream copy + faststart: juda tez, sifat yo'qolmaydi.
        process = await asyncio.create_subprocess_exec(
            "ffmpeg", "-y", "-i", input_path,
            "-map", "0:v:0", "-map", "0:a:0?",
            "-c", "copy", "-movflags", "+faststart", output_path,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
        )
    else:
        process = await asyncio.create_subprocess_exec(
            "ffmpeg", "-y", "-i", input_path,
            "-map", "0:v:0", "-map", "0:a:0?",
            "-c:v", "libx264", "-profile:v", "high", "-level", "5.1",
            "-pix_fmt", "yuv420p", "-preset", "veryfast", "-crf", "23",
            "-c:a", "aac", "-b:a", "128k", "-ar", "48000",
            "-movflags", "+faststart", output_path,
            stdout=asyncio.subprocess.DEVNULL, stderr=asyncio.subprocess.PIPE,
        )
    _, stderr = await process.communicate()
    if process.returncode != 0 or not os.path.isfile(output_path) or os.path.getsize(output_path) == 0:
        err = stderr.decode("utf-8", "ignore")[-1500:]
        await safe_remove(output_path)
        raise RuntimeError(f"FFmpeg video conversion failed: {err}")
    await safe_remove(input_path)
    return output_path

async def download_instagram_media(message: Message, url: str, shortcode: str):
    """Instagram post/reel/story/carousel media yuklash.
    Cookie fayli eskirgan bo'lsa Brave/Chromium login cookie'lari sinab ko'riladi.
    """
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    target_chat_id = message.chat.id

    if user_id in DOWNLOADING_USERS:
        await message.answer(get_text("download_in_progress_alert", lang))
        return
    if download_semaphore.locked():
        await message.answer("⚠️ Server band. Iltimos, biroz kuting.")
        return

    # Story URLlarida regex shortcode aslida username bo'lishi mumkin.
    # Shu sababli story uchun eski post cache'sini ishlatmaymiz.
    is_story = "/stories/" in url.lower()
    cache_key = shortcode if not is_story else ""
    cached_file = await db.get_cached_media(cache_key, quality="best") if cache_key else None
    if cached_file:
        file_id, media_type, _ = cached_file
        bot_username = (await message.bot.get_me()).username
        caption = f"Instagram | {get_text('downloaded_via_bot', lang, bot_username=bot_username)}"
        kb = instagram_post_actions_keyboard(shortcode, lang)
        try:
            if media_type == "video":
                await message.answer_video(file_id, caption=caption, reply_markup=kb)
            elif media_type == "photo":
                await message.answer_photo(file_id, caption=caption, reply_markup=kb)
            else:
                await message.answer_document(file_id, caption=caption, reply_markup=kb)
            return
        except Exception:
            logger.warning("Instagram cache file_id eskirgan, qayta yuklanadi.", exc_info=True)

    status_msg = await message.answer(get_text("insta_downloading", lang), parse_mode="HTML")
    DOWNLOADING_USERS.add(user_id)
    loop = asyncio.get_running_loop()
    downloads_dir = os.path.join(BASE_DIR, "downloads")
    os.makedirs(downloads_dir, exist_ok=True)
    unique_id = f"insta_{user_id}_{int(time.time() * 1000)}"
    downloaded_files: list[str] = []

    try:
        for auth_source in instagram_auth_sources():
            # Oldingi urinish qoldiqlarini tozalaymiz.
            for old_file in glob.glob(os.path.join(downloads_dir, unique_id + "*")):
                await safe_remove(old_file)

            opts = {
                "outtmpl": os.path.join(downloads_dir, unique_id + "_%(autonumber)02d.%(ext)s"),
                "quiet": True,
                "no_warnings": True,
                "ignoreerrors": False,
                "noplaylist": False,  # carousel uchun
                "format": "bestvideo+bestaudio/best",
                "merge_output_format": "mp4",
                "retries": 3,
                "fragment_retries": 3,
                "file_access_retries": 2,
                "socket_timeout": 30,
                "concurrent_fragment_downloads": 4,
                "source_address": "0.0.0.0",
                "nocheckcertificate": True,
                "http_headers": {
                    "User-Agent": (
                        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                        "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
                    ),
                    "Accept-Language": "en-US,en;q=0.9",
                },
            }
            apply_browser_auth(opts, auth_source)

            source_type, source_value = auth_source
            logger.info(
                "Instagram auth=%s",
                os.path.basename(source_value) if source_type == "file" else source_value or "none",
            )

            try:
                async with download_semaphore:
                    with yt_dlp.YoutubeDL(opts) as ydl:
                        info = await asyncio.wait_for(
                            loop.run_in_executor(
                                None, lambda: ydl.extract_info(url, download=True)
                            ),
                            timeout=180.0,
                        )

                if not info:
                    raise DownloadError("Instagram info olinmadi")

                # Hook'ga tayanmaymiz: yt-dlp merge tugagandan keyin katalogni tekshiramiz.
                candidates = []
                for fp in glob.glob(os.path.join(downloads_dir, unique_id + "*")):
                    if os.path.isfile(fp) and os.path.getsize(fp) > 0:
                        ext = os.path.splitext(fp)[1].lower()
                        if ext not in {".part", ".ytdl", ".temp"}:
                            candidates.append(fp)

                # Ba'zan autonumber chiqmaydi; info'dagi tayyor filename ham tekshiriladi.
                try:
                    prepared = ydl.prepare_filename(info)
                    if os.path.exists(prepared):
                        candidates.append(prepared)
                    base = os.path.splitext(prepared)[0]
                    for fp in glob.glob(base + ".*"):
                        if os.path.isfile(fp):
                            candidates.append(fp)
                except Exception:
                    pass

                # Faqat yakuniy media fayllarini tanlaymiz.
                seen = set()
                downloaded_files = []
                for fp in sorted(candidates):
                    fp = clean_path(fp)
                    if fp in seen:
                        continue
                    seen.add(fp)
                    ext = os.path.splitext(fp)[1].lower()
                    if ext in {".mp4", ".m4v", ".mov", ".webm", ".jpg", ".jpeg", ".png", ".webp", ".gif"}:
                        downloaded_files.append(fp)

                # Image-only carousel/story itemlari yt-dlp tomonidan "There is no video"
                # deb o'tkazib yuborilishi mumkin. Shu holatda sahifaning o'z JSON/HTML
                # media manbalaridan barcha rasm/video URLlarini olamiz. Storyda ham
                # faqat bitta item chiqib qolmasligi uchun web fallback tekshiriladi.
                if (not downloaded_files) or (is_story and len(downloaded_files) < 2):
                    try:
                        web_files = await asyncio.to_thread(
                            _instagram_web_media_download_sync,
                            url, auth_source, downloads_dir, unique_id,
                        )
                        if web_files:
                            # Story/carousel uchun web sahifadagi to'liq ro'yxat authoritative:
                            # yt-dlp image-only itemlarni o'tkazib yuborgan bo'lishi mumkin.
                            if is_story or not downloaded_files:
                                for old in list(downloaded_files):
                                    await safe_remove(old)
                                downloaded_files = list(web_files)
                            else:
                                downloaded_files.extend(web_files)
                    except Exception as web_exc:
                        logger.warning("Instagram web-media fallback xato: %s", web_exc, exc_info=True)

                # Dublikatlar va vaqtinchalik fayllarni chiqarib tashlaymiz.
                unique_downloads = []
                seen_downloads = set()
                for fp in downloaded_files:
                    fp = clean_path(fp)
                    if not os.path.isfile(fp) or os.path.getsize(fp) <= 0:
                        continue
                    if fp in seen_downloads:
                        continue
                    seen_downloads.add(fp)
                    unique_downloads.append(fp)
                downloaded_files = unique_downloads

                if not downloaded_files:
                    raise DownloadError("Instagram yakuniy media faylini yaratmadi")

                break

            except DownloadError as exc:
                text = str(exc).lower()
                logger.warning("Instagram %s xato: %s", auth_source, exc)
                # Login/cookie muammosi bo'lsa keyingi auth manbasiga o'tamiz.
                auth_markers = (
                    "login required", "log in", "cookie", "authentication",
                    "private", "sign in", "challenge", "403", "429",
                )
                if any(marker in text for marker in auth_markers):
                    continue
                # Umumiy xatoda ham boshqa auth manbasini sinab ko'ramiz.
                continue
            except Exception as exc:
                logger.warning("Instagram %s kutilmagan xato: %s", auth_source, exc, exc_info=True)
                continue

        if not downloaded_files:
            await status_msg.edit_text(
                "⚠️ Instagram media yuklanmadi. Brave/Chromium brauzerida Instagram akkauntingizga login qilinganini tekshiring."
            )
            return

        bot_username = (await message.bot.get_me()).username
        caption = f"Instagram | {get_text('downloaded_via_bot', lang, bot_username=bot_username)}"
        kb = instagram_post_actions_keyboard(shortcode, lang)
        files_sent = 0

        for filename in downloaded_files:
            if not os.path.exists(filename):
                continue
            try:
                ext = os.path.splitext(filename)[1].lower()
                size = os.path.getsize(filename)
                current_caption = caption if files_sent == 0 else None
                current_kb = kb if files_sent == 0 else None

                if ext in {".mp4", ".m4v", ".mov", ".webm"}:
                    # Instagram ba'zan HEVC/VP9 yoki noodatiy audio beradi.
                    # Telegram va eski Android/iPhone/Windows qurilmalari uchun
                    # universal H.264 + AAC + yuv420p MP4 ga o'tkazamiz.
                    compatible_file = await ensure_telegram_compatible_video(filename)
                    filename = compatible_file
                    size = os.path.getsize(filename)
                    media_width, media_height, media_duration = await probe_video_metadata(filename)
                    sent = await smart_send_video(
                        message.bot, target_chat_id, filename,
                        current_caption, width=media_width, height=media_height,
                        duration=media_duration, reply_markup=current_kb
                    )
                    if (
                        files_sent == 0 and sent and getattr(sent, "video", None)
                        and size <= 50 * 1024 * 1024
                    ):
                        await db.save_cached_media(
                            cache_key, sent.video.file_id, "video", "best", 0,
                            title="Instagram Video",
                        )
                elif ext in {".jpg", ".jpeg", ".png", ".webp", ".gif"}:
                    # Katta/WebP/GIF rasmlar uchun document fallback.
                    sent = None
                    if ext in {".jpg", ".jpeg", ".png"} and size <= 10 * 1024 * 1024:
                        try:
                            sent = await message.answer_photo(
                                FSInputFile(filename),
                                caption=current_caption,
                                reply_markup=current_kb,
                            )
                        except Exception:
                            logger.warning("Instagram rasmni photo sifatida yuborib bo'lmadi, document sinovdan o'tadi.")
                    if sent is None:
                        sent = await message.answer_document(
                            FSInputFile(filename),
                            caption=current_caption,
                            reply_markup=current_kb,
                        )
                    if (
                        files_sent == 0 and sent and getattr(sent, "photo", None)
                        and cache_key
                    ):
                        await db.save_cached_media(
                            cache_key, sent.photo.file_id, "photo", "best", 0,
                            title="Instagram Photo",
                        )
                else:
                    sent = await message.answer_document(
                        FSInputFile(filename),
                        caption=current_caption,
                        reply_markup=current_kb,
                    )
                files_sent += 1
            except Exception as exc:
                logger.error("Instagram fayl yuborishda xato %s: %s", filename, exc, exc_info=True)
            finally:
                await safe_remove(filename)

        if files_sent:
            await status_msg.delete()
            await db.add_download_stat(user_id, "instagram")
        else:
            await status_msg.edit_text("⚠️ Instagram fayli Telegramga yuborilmadi.")
    except asyncio.TimeoutError:
        logger.error("Instagram timeout: %s", url)
        await status_msg.edit_text("⚠️ Instagram yuklash vaqti tugadi. Qayta urinib ko'ring.")
    except Exception as exc:
        logger.error("Instagram download error: %s", exc, exc_info=True)
        try:
            await status_msg.edit_text(get_text("error", lang))
        except Exception:
            pass
    finally:
        DOWNLOADING_USERS.discard(user_id)
        for fp in glob.glob(os.path.join(downloads_dir, unique_id + "*")):
            await safe_remove(fp)

async def _perform_generic_video_download(message: Message, url: str, user_id: int, bot: Bot):
    """Facebook uchun umumiy yuklash funksiyasi"""
    lang = await get_user_lang(user_id)
    target_chat_id = message.chat.id
    
    if user_id in DOWNLOADING_USERS:
        return # Jim turamiz

    # Server yuklamasini tekshirish
    if download_semaphore.locked():
        await message.answer("⚠️ Server yuklama bilan band. Iltimos, biroz kuting.")
        return

    # URLni tozalash
    url_match = re.search(r'(https?://[^\s]+)', url)
    clean_url = url_match.group(0) if url_match else url.strip()

    # 1. URLni tozalash va keshni tekshirish
    cached_file = await db.get_cached_media(clean_url)
    if cached_file:
        file_id, _, _ = cached_file
        bot_username = (await bot.get_me()).username
        caption = f"Facebook | {get_text('downloaded_via_bot', lang, bot_username=bot_username)}"
        kb = video_actions_keyboard(lang)
        
        try:
            await message.answer_video(file_id, caption=caption, reply_markup=kb)
            return
        except Exception as e:
            logger.warning(f"Keshdagi faylni yuborishda xato (qayta yuklanadi): {e}")
            # Agar keshdagi fayl ishlamasa, davom etamiz va qayta yuklaymiz

    status_msg = await message.answer(get_text("generic_downloading", lang), parse_mode="HTML")
    DOWNLOADING_USERS.add(user_id)
    
    try:
        loop = asyncio.get_event_loop()
        unique_id = f"gen_{user_id}_{int(time.time())}"
        ydl_opts = {
            'format': 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best',
            'merge_output_format': 'mp4',
            'nocheckcertificate': True, 'geo_bypass': True,
            'outtmpl': f"downloads/{unique_id}.%(ext)s",
            'quiet': True, 'geo_bypass': True, 'ignoreerrors': False,
            'http_headers': {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36',
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            },
            'extractor_args': {'facebook': {'remote_components': True}}, 
            'concurrent_fragment_downloads': 30,
            'socket_timeout': 30,
            'sleep_interval': 3,
        }

        async with download_semaphore:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = await loop.run_in_executor(None, lambda: ydl.extract_info(url, download=True))
                filename = clean_path(ydl.prepare_filename(info))
                title = info.get('title', 'Video')
            if info is None:
                raise DownloadError("Failed to extract info for generic video download.")
            
        # Fayl mavjudligini va hajmini tekshirish
        if not os.path.exists(filename) or os.path.getsize(filename) == 0:
            logger.error(f"Facebook video yuklanmadi yoki bo'sh: {filename}")
            await status_msg.edit_text(get_text("error", lang))
            return

        bot_username = (await bot.get_me()).username
        # Facebook uchun nomni olib tashlash (faqat bot linki)
        caption = f"Facebook | {get_text('downloaded_via_bot', lang, bot_username=bot_username)}"
        
        if os.path.exists(filename):
            video_file = FSInputFile(filename)
            
            # Saqlash tugmasi
            kb = video_actions_keyboard(lang)

            # Aqlli yuborish (Bot tomonidan yuborilishi uchun)
            sent = await smart_send_video(bot, target_chat_id, filename, caption, width=info.get('width'), height=info.get('height'), reply_markup=kb)
            
            if sent and getattr(sent, "video", None) and os.path.getsize(filename) <= 50 * 1024 * 1024:
                await db.save_cached_media(clean_url, sent.video.file_id, "video", "best", os.path.getsize(filename), title=title)

            await status_msg.delete()
            await safe_remove(filename)
            await db.add_download_stat(user_id, "generic_video")
        else:
            await status_msg.edit_text(get_text("error", lang))
            
    except Exception as e:
        logger.error(f"Generic video download error: {e}")
        await status_msg.edit_text(get_text("error", lang))
    finally:
        DOWNLOADING_USERS.discard(user_id)

async def _perform_youtube_download(
    message: Message,
    video_id: str,
    user_id: int,
    bot: Bot,
    resolution: str = None,
    callback: CallbackQuery = None,
    hide_title: bool = False,
    is_shorts: bool = False,
):
    """YouTube yuklash: kam urinish, tez timeout, barqaror MP4/H.264 chiqishi."""
    target_chat_id = message.chat.id if message else (
        callback.message.chat.id if callback else user_id
    )
    lang = await get_user_lang(user_id)

    if user_id in DOWNLOADING_USERS:
        msg_text = get_text("download_in_progress_alert", lang)
        if callback:
            await callback.answer(msg_text, show_alert=True)
        return

    if download_semaphore.locked():
        msg_text = "⚠️ Server band. Iltimos, biroz kuting."
        if callback:
            await callback.answer(msg_text, show_alert=True)
        else:
            await message.answer(msg_text)
        return

    cache_key = f"{video_id}_{resolution if resolution else 'best'}"
    cached_file = await db.get_cached_media(cache_key, quality=resolution)
    if cached_file:
        cached_ref, _, _ = cached_file
        bot_username = (await bot.get_me()).username
        caption = get_text("downloaded_via_bot", lang, bot_username=bot_username)
        kb = video_actions_keyboard(
            lang, video_id=video_id, is_youtube=True, is_shorts=is_shorts
        )
        try:
            if callback:
                await callback.message.delete()
            if isinstance(cached_ref, str) and cached_ref.startswith("channel:"):
                # Katta video: userbot kanalga joylagan xabarning IDsi orqali
                # Bot API copyMessage bilan BOT nomidan foydalanuvchiga yuboriladi.
                channel_msg_id = int(cached_ref.split(":", 1)[1])
                sent = await bot.copy_message(
                    chat_id=target_chat_id,
                    from_chat_id=int(UPLOAD_CHANNEL_ID),
                    message_id=channel_msg_id,
                    caption=caption,
                    parse_mode="HTML",
                    reply_markup=kb,
                )
            else:
                sent = await (callback.message.answer_video(cached_ref, caption=caption, reply_markup=kb) if callback else message.answer_video(cached_ref, caption=caption, reply_markup=kb))
            return sent
        except Exception:
            logger.warning("YouTube cache media yaroqsiz, qayta yuklanadi.", exc_info=True)

    if callback:
        await callback.answer("YouTube video yuklanmoqda... 🚀")

    loading_text = (
        get_text("yt_downloading_res", lang, resolution=resolution)
        if resolution else get_text("yt_video_loading", lang)
    )
    if callback:
        status_msg = await callback.message.edit_text(
            loading_text, parse_mode="HTML"
        )
    else:
        status_msg = await message.answer(loading_text, parse_mode="HTML")

    url = f"https://www.youtube.com/watch?v={video_id}"
    DOWNLOADING_USERS.add(user_id)
    downloads_dir = os.path.join(BASE_DIR, "downloads")
    os.makedirs(downloads_dir, exist_ok=True)

    # "page needs to be reloaded" format xatosi emas — keyingi formatni
    # qayta-qayta urish serverni faqat qotirib qo'yadi. Har bir auth uchun
    # faqat bitta asosiy format va bitta sodda fallback ishlatiladi.
    max_height = int(resolution) if resolution and str(resolution).isdigit() else 1080
    format_options = [
        f"bestvideo[height<={max_height}]+bestaudio/best[height<={max_height}]/best",
        "best[height<=720]/best",
    ]

    last_exception = None
    success = False
    generated_files = []

    try:
        for auth_source in youtube_auth_sources():
            source_type, source_value = auth_source
            auth_label = (
                os.path.basename(source_value)
                if source_type == "file"
                else source_value or "cookiesiz"
            )

            # Browser cookie bazasini har bir format uchun qayta o'qimaymiz.
            for fmt_index, fmt in enumerate(format_options):
                if success:
                    break

                filename = os.path.join(
                    downloads_dir,
                    f"yt_{video_id}_{user_id}_{int(time.time() * 1000)}.%(ext)s",
                )
                try:
                    loop = asyncio.get_running_loop()
                    last_update_time = [time.time()]
                    hook = partial(
                        progress_hook,
                        bot=bot,
                        message=status_msg,
                        last_update_time=last_update_time,
                        loop=loop,
                        lang=lang,
                        finished_text_key="yt_video_processing",
                    )

                    ydl_opts = get_youtube_ydl_opts(
                        fmt=fmt,
                        outtmpl=filename,
                        progress_hook=hook,
                        extra={
                            "add_metadata": True,
                            # Formatlarni ketma-ket almashtirib qotib qolmasin.
                            "retries": 2,
                            "fragment_retries": 2,
                            "file_access_retries": 2,
                            "sleep_interval": 0,
                            "max_sleep_interval": 0,
                            "concurrent_fragment_downloads": 8,
                        },
                    )
                    apply_youtube_auth(ydl_opts, auth_source)
                    if source_type == "none":
                        # Cookiesiz rejimda bot-detectionni kamaytirish uchun PO-token talab qilmaydigan
                        # clientlardan foydalanamiz. Authenticated rejimda esa yt-dlp ning current default
                        # client selectioni ishlaydi.
                        ydl_opts.setdefault("extractor_args", {}).setdefault("youtube", {})[
                            "player_client"
                        ] = ["tv", "web_embedded"]

                    logger.info(
                        "YouTube: Auth=%s, Format=%s",
                        auth_label,
                        fmt,
                    )

                    async with download_semaphore:
                        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                            info = await asyncio.wait_for(
                                loop.run_in_executor(
                                    None,
                                    lambda: ydl.extract_info(
                                        url, download=True
                                    ),
                                ),
                                timeout=90.0,
                            )

                            if not info:
                                raise DownloadError(
                                    "YouTube ma'lumotlarini olib bo'lmadi."
                                )

                            prepared = clean_path(ydl.prepare_filename(info))
                            candidates = []

                            # prepare_filename MP4 bo'lmasligi mumkin; yt-dlp
                            # merge qilgan yakuniy faylni ham qidiramiz.
                            base = os.path.splitext(prepared)[0]
                            for fp in glob.glob(base + ".*"):
                                if (
                                    os.path.isfile(fp)
                                    and not fp.endswith(
                                        (".part", ".ytdl", ".temp")
                                    )
                                    and os.path.getsize(fp) > 0
                                ):
                                    candidates.append(clean_path(fp))

                            prefix = os.path.splitext(os.path.basename(filename))[0]
                            for fp in glob.glob(
                                os.path.join(downloads_dir, prefix + "*")
                            ):
                                if (
                                    os.path.isfile(fp)
                                    and not fp.endswith(
                                        (".part", ".ytdl", ".temp")
                                    )
                                    and os.path.getsize(fp) > 0
                                ):
                                    candidates.append(clean_path(fp))

                            mp4_candidates = [
                                fp for fp in dict.fromkeys(candidates)
                                if os.path.splitext(fp)[1].lower() == ".mp4"
                            ]
                            final_file = (
                                max(
                                    mp4_candidates,
                                    key=os.path.getsize,
                                )
                                if mp4_candidates
                                else (
                                    max(candidates, key=os.path.getsize)
                                    if candidates else None
                                )
                            )

                            if not final_file:
                                raise DownloadError(
                                    "YouTube yakuniy video fayli topilmadi."
                                )

                            # Yakuniy faylni ham universal H.264/AAC MP4 qilamiz.
                            # Bu faqat yuklab olingan faylga qo'llanadi, Telegram
                            # yuborishdan oldin format mosligini kafolatlaydi.
                            final_file = await ensure_telegram_compatible_video(final_file)

                            title = info.get("title", "Video")
                            width = info.get("width")
                            height = info.get("height")
                            duration = info.get("duration")

                    bot_username = (await bot.get_me()).username
                    if hide_title:
                        caption = get_text(
                            "downloaded_via_bot",
                            lang,
                            bot_username=bot_username,
                        )
                    else:
                        quality_text = (
                            f"\n💿 Sifat: {resolution}p"
                            if resolution else ""
                        )
                        caption = (
                            f"📹 <b>{escape(title)}</b>"
                            f"{quality_text}\n\n"
                            f"{get_text('downloaded_via_bot', lang, bot_username=bot_username)}"
                        )

                    kb = video_actions_keyboard(
                        lang,
                        video_id=video_id,
                        is_youtube=True,
                        is_shorts=is_shorts,
                    )

                    sent = await smart_send_video(
                        bot,
                        target_chat_id,
                        final_file,
                        caption,
                        width=width,
                        height=height,
                        duration=duration,
                        reply_markup=kb,
                    )

                    if sent is None:
                        raise DownloadError(
                            "Video Telegramga yuborilmadi (hajm yoki userbot muammosi)."
                        )

                    cache_ref = None
                    if isinstance(sent, dict) and sent.get("channel_message_id"):
                        cache_ref = f"channel:{int(sent['channel_message_id'])}"
                    elif getattr(sent, "video", None) and os.path.getsize(final_file) <= 50 * 1024 * 1024:
                        cache_ref = sent.video.file_id
                    if cache_ref:
                        await db.save_cached_media(
                            cache_key, cache_ref, "video", resolution,
                            os.path.getsize(final_file), title=title,
                        )

                    await safe_remove(final_file)
                    await status_msg.delete()
                    await db.add_download_stat(user_id, "video")
                    success = True
                    generated_files.append(final_file)

                except asyncio.TimeoutError:
                    last_exception = TimeoutError(
                        "YouTube yuklash 120 soniyada tugamadi."
                    )
                    logger.warning(
                        "YouTube timeout: auth=%s format=%s",
                        auth_label,
                        fmt,
                    )
                    # Browser cookie o'qilishi yoki YouTube serveri osilib
                    # qolsa, boshqa formatlarni behuda urmaymiz.
                    break

                except DownloadError as exc:
                    last_exception = exc
                    text = str(exc).lower()
                    logger.warning(
                        "YouTube xato: auth=%s format=%s: %s",
                        auth_label,
                        fmt,
                        exc,
                    )

                    # Aynan sizdagi xato: bu format muammosi emas.
                    # Keyingi formatga emas, keyingi auth/clientga o'tamiz.
                    reload_markers = (
                        "the page needs to be reloaded",
                        "page needs to be reloaded",
                        "playability status: unplayable",
                        "tv_downgraded",
                        "sabr",
                    )
                    auth_markers = (
                        "sign in to confirm",
                        "authentication",
                        "login required",
                        "cookies",
                        "private",
                        "challenge",
                    )

                    if any(x in text for x in reload_markers):
                        logger.warning(
                            "YouTube client/playability muammosi. "
                            "Keyingi auth manbasi sinab ko'riladi."
                        )
                        break

                    if any(x in text for x in auth_markers):
                        break

                    if "requested format is not available" in text:
                        # Faqat bir marta sodda fallback format.
                        if fmt_index < len(format_options) - 1:
                            continue
                        break

                    # Boshqa xatoda ham auth manbasini almashtiramiz.
                    break

                except Exception as exc:
                    last_exception = exc
                    logger.warning(
                        "YouTube auth manbasi ishlamadi: auth=%s: %s",
                        auth_label,
                        exc,
                        exc_info=True,
                    )
                    # Browser cookie o'qilmasa, boshqa browser yoki cookie fayliga o'tamiz.
                    break

            if success:
                break

    finally:
        DOWNLOADING_USERS.discard(user_id)
        # Qoldiq .part/.ytdl va muvaffaqiyatsiz fayllarni tozalash.
        cleanup_prefix = f"yt_{video_id}_{user_id}_"
        for fp in glob.glob(
            os.path.join(downloads_dir, cleanup_prefix + "*")
        ):
            if fp not in generated_files:
                await safe_remove(fp)

    if not success:
        logger.error(
            "YouTube download error: %s",
            last_exception,
            exc_info=True,
        )
        err_msg = get_text("error", lang)
        try:
            await status_msg.edit_text(err_msg, parse_mode="HTML")
        except Exception:
            try:
                if callback:
                    await callback.message.answer(err_msg)
                else:
                    await message.answer(err_msg)
            except Exception:
                pass

# ============================================================
# GLOBAL LINK HANDLER (YouTube/Instagram/Facebook)
# ============================================================
@router.message(F.text, StateFilter(None))
async def global_link_handler(message: Message, state: FSMContext):
    """Global link handler for YouTube, Instagram and Facebook"""
    query = message.text
    user_id = message.from_user.id

    # YouTube
    yt_match = YOUTUBE_PATTERN.search(query)
    if yt_match:
        video_id = yt_match.group(1)
        if "shorts" in query.lower():
            await _perform_youtube_download(message, video_id, user_id, message.bot, hide_title=False, is_shorts=True)
        else:
            lang = await get_user_lang(user_id)
            await message.answer(
                get_text("yt_video_found", lang),
                parse_mode="HTML",
                reply_markup=youtube_format_keyboard(video_id, lang)
            )
        return

    # Instagram
    insta_match = INSTAGRAM_PATTERN.search(query)
    if insta_match:
        shortcode = insta_match.group(2)
        await download_instagram_media(message, query, shortcode)
        return
        
    # Facebook
    if FACEBOOK_PATTERN.search(query):
        await _perform_generic_video_download(message, query, user_id, message.bot)
        return

# ============================================================
# AVTOMATIK SAQLASH HANDLERLARI (Audio va Video)
# ============================================================
@router.message(F.audio, StateFilter(None))
async def auto_save_audio_handler(message: Message, state: FSMContext):
    """Foydalanuvchi audio yuborganda avtomatik saqlash (faqat asosiy holatda)"""
    # Agar foydalanuvchi biror jarayonda bo'lsa (masalan, ovoz->matn), aralashmaymiz
    current_state = await state.get_state()
    if current_state in [UserStates.voice_to_text, UserStates.shazam_mode]:
        return

    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    duration = message.audio.duration
    title = message.audio.title or message.audio.file_name or "Audio"
    
    file_id = message.audio.file_id
    # Bazaga saqlash
    if await db.save_music(user_id, file_id, title, duration):
        await db.add_download_stat(user_id, "user_audio_upload")
        await message.reply(get_text("audio_received_saved", lang))
    else:
        # Agar avval saqlangan bo'lsa ham, foydalanuvchiga bildiramiz
        await message.reply(get_text("music_already_saved", lang))

@router.message(F.video, StateFilter(None))
async def auto_save_video_handler(message: Message, state: FSMContext):
    """Foydalanuvchi video yuborganda avtomatik saqlash (faqat asosiy holatda)"""
    # Agar foydalanuvchi biror jarayonda bo'lsa (masalan, video->mp3, dumaloq video), aralashmaymiz
    current_state = await state.get_state()
    if current_state in [UserStates.video_to_mp3, UserStates.round_video, UserStates.shazam_mode, UserStates.ads_media, AdminStates.upload_video_guide]:
        return

    user_id = message.from_user.id
    lang = await get_user_lang(user_id)
    
    caption = message.caption or message.video.file_name or "Video"
    
    # Captionni tozalash
    clean_caption = caption.split("\n")[0].strip()
    if len(clean_caption) > 50:
        clean_caption = clean_caption[:47] + "..."
    
    file_id = message.video.file_id
    # Bazaga saqlash
    if await db.save_video(user_id, file_id, clean_caption):
        await db.add_download_stat(user_id, "user_video_upload")
        await message.reply(get_text("video_received_saved", lang))
    else:
        await message.reply(get_text("video_already_saved", lang))


# ============================================================
# Bosh menyu / Bekor qilish (universal)
# ============================================================
async def go_to_main_menu(message_or_callback: Union[Message, CallbackQuery], state: FSMContext):
    """
    Bosh menyuga qaytish uchun markaziy funksiya. FSM holatini tozalaydi,
    xabarni tahrirlaydi va menyuni ko'rsatadi.
    """
    message_obj = message_or_callback.message if isinstance(message_or_callback, CallbackQuery) else message_or_callback
    user_id = message_or_callback.from_user.id

    # ReplyKeyboard'ni olib tashlash
    current_state = await state.get_state() if state else None
    needs_kb_remove = current_state in [UserStates.location.state, UserStates.edit_location.state, UserStates.phone.state, UserStates.edit_phone.state]

    # Bosh menyuga qaytganda FSM holatini tozalaymiz
    if state:
        await clear_state_preserve_session(state)

    is_admin = await is_user_admin(user_id)
    lang = await get_user_lang(user_id)
    text = get_text("welcome_main", lang)

    # Foydalanuvchi ismi bilan salomlashish uchun
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else message_or_callback.from_user.first_name
    text = get_text("welcome_ready", lang, name=escape(display_name, quote=False))
    kb = main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name) # noqa

    if isinstance(message_or_callback, CallbackQuery):
        await safe_edit_message(message_or_callback, text, reply_markup=kb)
        await message_or_callback.answer() # click effektini ko'rsatish
    else:
        # Message'dan kelganda, yangi xabar yuboramiz
        await message_obj.answer(text, reply_markup=kb)

    if needs_kb_remove:
        try:
            remover_msg = await message_obj.answer("...", reply_markup=ReplyKeyboardRemove())
            await remover_msg.delete()
        except Exception as e:
            logger.warning(f"ReplyKeyboard remover xatosi: {e}")


@router.callback_query(F.data == "menu_main")
async def back_to_main_callback(callback: CallbackQuery, state: FSMContext):
    await go_to_main_menu(callback, state)

@router.callback_query(F.data == "cancel")
async def cancel_callback(callback: CallbackQuery, state: FSMContext):
    """
    Universal "Bekor qilish" tugmasi uchun handler.
    Bu funksiya har qanday jarayonni to'xtatadi va foydalanuvchini
    bosh menyuga qaytaradi, shu bilan birga FSM holatini tozalaydi va
    qolib ketgan ReplyKeyboard'larni olib tashlaydi.
    """
    await callback.answer(get_text("cancelled_text", await get_user_lang(callback.from_user.id)))
    # Markaziy `go_to_main_menu` funksiyasiga yo'naltirish orqali FSM holatini tozalash va klaviaturani olib tashlash
    await go_to_main_menu(callback, state)


# ============================================================
# Profil
# ============================================================
async def send_profile_view(message_obj: Message, user_id: int, profile_text: str, photo_id: Optional[str], has_profile: bool, lang: str):
    """Profilni rasm bilan yoki rasmsiz yuborish uchun yordamchi funksiya"""
    kb = await profile_keyboard(has_profile, lang, user_id)
    if photo_id:
        try:
            await message_obj.answer_photo(
                photo=photo_id,
                caption=profile_text,
                parse_mode="HTML",
                reply_markup=kb
            )
        except TelegramBadRequest: # Agar rasm topilmasa
            await message_obj.answer(profile_text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)
    else:
        await message_obj.answer(profile_text, parse_mode="HTML", reply_markup=kb, disable_web_page_preview=True)


@router.callback_query(F.data == "menu_profile")
async def profile_handler(callback: CallbackQuery, bot: Bot):
    user_id = callback.from_user.id
    user = await db.get_user(user_id) # Profil bo'lmasa ham user bazada bo'ladi (middleware qo'shadi)
    if not user:
        await go_to_main_menu(callback, None) # Xato bo'lsa menyuga qaytarish
        return

    # Profil rasmini yangilash va olish
    try:
        photos = await bot.get_user_profile_photos(user_id, limit=1)
        if photos.total_count > 0:
            photo_id = photos.photos[0][-1].file_id
            await db.update_user_field(user_id, "photo_id", photo_id)
        else:
            photo_id = None
    except Exception as e:
        logger.error(f"Profil rasmini olishda xato: {e}")
        photo_id = None

    lang = await get_user_lang(user_id) # Get language after potential profile update
    has_profile = await db.has_profile(user_id)
    
    # Agar profil bo'lmasa, maxsus xabar ko'rsatish
    if not has_profile:
        name = callback.from_user.first_name
        no_profile_text = ( # Foydalanuvchi ismi HTML dan himoyalangan
            f"👋 Salom, {escape(name)}!\n\n"
            f"🚫 <b>Siz profilingizni to'ldirmagansiz.</b>\n"
            f"📉 Sizning profil holatingiz: <b>Yomon</b> 👎\n\n"
            f"Iltimos, bot imkoniyatlaridan to'liq foydalanish uchun '➕ Profil kiritish' tugmasini bosing."
        )
        await safe_edit_message(callback, no_profile_text, reply_markup=await profile_keyboard(False, lang, user_id))
        return

    profile_text = await get_user_profile_text(user, lang)

    await callback.message.delete()
    await send_profile_view(callback.message, user_id, profile_text, photo_id, has_profile, lang)
    await callback.answer()

# --- Profil yaratish/tahrirlash ---
@router.callback_query(F.data == "create_profile")
async def create_profile_callback(callback: CallbackQuery, state: FSMContext):
    # Sharh: Profil yaratishda xabarlarni alohida yubormasdan, mavjudini tahrirlaymiz.
    # Bu kodni toza va foydalanuvchi uchun qulay qiladi.
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.full_name)
    await callback.message.edit_text(
        f"{get_text('privacy_notice', lang)}\n\n"
        f"Iltimos, <b>ism va familyangizni</b> kiriting: 👤",
        parse_mode="HTML",
        reply_markup=back_to_main_keyboard(lang)
    )
    await callback.answer()


@router.message(StateFilter(UserStates.full_name))
async def full_name_handler(message: Message, state: FSMContext):
    await db.update_user_field(message.from_user.id, "full_name", message.text)
    lang = await get_user_lang(message.from_user.id)
    await state.set_state(UserStates.region)
    await message.answer("<b>Viloyatni tanlang:</b> 🌍", parse_mode="HTML", reply_markup=regions_keyboard(lang))


@router.callback_query(StateFilter(UserStates.region), lambda c: c.data.startswith("region_"))
async def region_callback(callback: CallbackQuery, state: FSMContext):
    region = callback.data.split("_", 1)[1]
    lang = await get_user_lang(callback.from_user.id)
    await db.update_user_field(callback.from_user.id, "region", region)
    await state.set_state(UserStates.district)

    kb = districts_keyboard(region, lang)
    if kb:
        await callback.message.edit_text("<b>Tumanni tanlang:</b> 🏘️", parse_mode="HTML", reply_markup=kb)
    else:
        await callback.message.edit_text("<b>Tumanni kiriting:</b> 🏘️", parse_mode="HTML")
    await callback.answer()


@router.message(StateFilter(UserStates.region))
async def region_text_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    await db.update_user_field(message.from_user.id, "region", message.text)
    await state.set_state(UserStates.district)
    await message.answer(get_text("enter_district_prompt", lang), reply_markup=cancel_keyboard(lang))

@router.callback_query(StateFilter(UserStates.district), lambda c: c.data.startswith("district_"))
async def district_callback(callback: CallbackQuery, state: FSMContext):
    district = callback.data.split("_", 1)[1]
    lang = await get_user_lang(callback.from_user.id)
    await db.update_user_field(callback.from_user.id, "district", district)
    await state.set_state(UserStates.neighborhood)

    kb = neighborhoods_keyboard(district, lang)
    if kb:
        await callback.message.edit_text(f"<b>{get_text('select_neighborhood_prompt', lang)}</b>", parse_mode="HTML", reply_markup=kb)
    else:
        await callback.message.edit_text(f"<b>{get_text('enter_neighborhood_prompt', lang)}</b>", parse_mode="HTML")
    await callback.answer()


@router.message(StateFilter(UserStates.district))
async def district_text_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    await db.update_user_field(message.from_user.id, "district", message.text)
    await state.set_state(UserStates.neighborhood)
    await message.answer("Mahallani kiriting: 🏠", reply_markup=cancel_keyboard(lang))


@router.callback_query(StateFilter(UserStates.neighborhood), lambda c: c.data.startswith("neigh_"))
async def neighborhood_callback(callback: CallbackQuery, state: FSMContext):
    neighborhood = callback.data.split("_", 1)[1]
    await db.update_user_field(callback.from_user.id, "neighborhood", neighborhood)
    lang = await get_user_lang(callback.from_user.id)
    await state.set_state(UserStates.phone)
    await callback.message.delete()
    await callback.message.answer(get_text("enter_phone_prompt", lang), reply_markup=phone_keyboard(lang))
    await callback.answer()


@router.message(StateFilter(UserStates.neighborhood))
async def neighborhood_text_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    await db.update_user_field(message.from_user.id, "neighborhood", message.text)
    await state.set_state(UserStates.phone)
    await message.answer(get_text("enter_phone_prompt", lang), reply_markup=phone_keyboard(lang))


@router.message(StateFilter(UserStates.phone), F.content_type.in_([ContentType.TEXT, ContentType.CONTACT]))
async def phone_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    
    if message.contact:
        phone = message.contact.phone_number
    else:
        phone = message.text.strip()

    # Raqamni tozalash (faqat raqamlar va boshidagi + belgisi)
    clean_phone = re.sub(r'[^\d+]', '', phone)
    
    # Agar raqam faqat raqamlardan iborat bo'lsa va + bo'lmasa
    if clean_phone.isdigit():
        # Agar 9 xonali bo'lsa (O'zbekiston ichki formati), +998 qo'shamiz
        if len(clean_phone) == 9:
             formatted_phone = f"+998{clean_phone}"
        # Agar 12 xonali bo'lib 998 bilan boshlansa
        elif len(clean_phone) == 12 and clean_phone.startswith("998"):
             formatted_phone = f"+{clean_phone}"
        else:
             formatted_phone = f"+{clean_phone}"
    else:
        formatted_phone = clean_phone
    
    # Minimal uzunlik tekshiruvi (xalqaro standartlarga moslashish uchun 7 dan 15 gacha)
    digits_only = re.sub(r'\D', '', formatted_phone)
    if len(digits_only) < 7 or len(digits_only) > 15:
        await message.reply("⚠️ Iltimos, to'g'ri telefon raqam kiriting.", reply_markup=phone_keyboard(lang))
        return

    await db.update_user_field(message.from_user.id, "phone", formatted_phone)
    await state.set_state(UserStates.location)
    await message.answer("Raqam qabul qilindi! ✅", reply_markup=ReplyKeyboardRemove())
    await message.reply("<b>Joylashuvingizni ulashing:</b> 📍", parse_mode="HTML", reply_markup=location_keyboard(lang))


@router.message(StateFilter(UserStates.location), F.content_type == ContentType.LOCATION)
async def location_handler(message: Message, state: FSMContext):
    if message.location:
        loc = f"{message.location.latitude},{message.location.longitude}"
        await db.update_user_field(message.from_user.id, "location", loc)
    await state.clear()
    await message.answer("Joylashuv qabul qilindi! ✅", reply_markup=ReplyKeyboardRemove())
    is_admin = await is_user_admin(message.from_user.id)
    lang = await get_user_lang(message.from_user.id)
    await message.answer("✅ <b>Profil to'liq saqlandi!</b>", parse_mode="HTML", reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang))


@router.message(StateFilter(UserStates.location))
async def location_text_handler(message: Message, state: FSMContext):
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await go_to_main_menu(message, state)
        return
    lang = await get_user_lang(message.from_user.id)
    await message.answer("Iltimos, joylashuvni ulashing yoki bosh menyuga qayting: 📍", reply_markup=location_keyboard(lang))


# --- Profil tahrirlash ---
@router.callback_query(F.data == "edit_profile")
async def edit_profile_callback(callback: CallbackQuery):
    lang = await get_user_lang(callback.from_user.id)
    text = get_text("edit_profile_prompt", lang)
    kb = edit_profile_keyboard(lang)
    
    # Rasm bo'lsa ham tahrirlash uchun
    await safe_edit_message(callback, text, reply_markup=kb)
    await callback.answer(get_text("editing_mode", lang))


@router.callback_query(F.data == "edit_full_name")
async def edit_full_name_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_full_name)
    lang = await get_user_lang(callback.from_user.id)
    await callback.message.edit_text(get_text("enter_new_fullname", lang), parse_mode="HTML", reply_markup=cancel_keyboard(lang))
    await callback.answer()


@router.message(StateFilter(UserStates.edit_full_name))
async def edit_full_name_handler(message: Message, state: FSMContext):
    await db.update_user_field(message.from_user.id, "full_name", message.text)
    await finish_profile_edit(message, state)

@router.callback_query(F.data == "edit_region")
async def edit_region_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_region)
    lang = await get_user_lang(callback.from_user.id)
    await callback.message.edit_text(get_text("enter_new_region", lang), parse_mode="HTML", reply_markup=regions_keyboard(lang))
    await callback.answer()


@router.callback_query(StateFilter(UserStates.edit_region), lambda c: c.data.startswith("region_"))
async def edit_region_handler(callback: CallbackQuery, state: FSMContext):
    region = callback.data.split("_", 1)[1]
    await db.update_user_field(callback.from_user.id, "region", region)
    await finish_profile_edit(callback, state)

@router.callback_query(F.data == "edit_district")
async def edit_district_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_district)
    user = await db.get_user(callback.from_user.id)
    lang = await get_user_lang(callback.from_user.id)
    region = user[5] if user else None
    if region and region in DISTRICTS:
        await callback.message.edit_text(get_text("enter_new_district", lang), parse_mode="HTML", reply_markup=districts_keyboard(region, lang))
    else:
        await callback.message.edit_text(get_text("enter_new_district_input", lang), parse_mode="HTML", reply_markup=cancel_keyboard(lang))
    await callback.answer()


@router.callback_query(StateFilter(UserStates.edit_district), lambda c: c.data.startswith("district_"))
async def edit_district_handler(callback: CallbackQuery, state: FSMContext):
    district = callback.data.split("_", 1)[1]
    await db.update_user_field(callback.from_user.id, "district", district)
    await finish_profile_edit(callback, state)

@router.message(StateFilter(UserStates.edit_district))
async def edit_district_text_handler(message: Message, state: FSMContext):
    await db.update_user_field(message.from_user.id, "district", message.text)
    await finish_profile_edit(message, state)

@router.callback_query(F.data == "edit_neighborhood")
async def edit_neighborhood_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_neighborhood)
    user = await db.get_user(callback.from_user.id)
    lang = await get_user_lang(callback.from_user.id)
    district = user[6] if user else None
    kb = neighborhoods_keyboard(district, lang) if district else None
    if kb:
        await callback.message.edit_text(get_text("enter_new_neighborhood", lang), parse_mode="HTML", reply_markup=kb)
    else:
        await callback.message.edit_text(get_text("enter_new_neighborhood_input", lang), parse_mode="HTML", reply_markup=cancel_keyboard(lang))
    await callback.answer()


@router.callback_query(StateFilter(UserStates.edit_neighborhood), lambda c: c.data.startswith("neigh_"))
async def edit_neighborhood_handler(callback: CallbackQuery, state: FSMContext):
    neighborhood = callback.data.split("_", 1)[1]
    await db.update_user_field(callback.from_user.id, "neighborhood", neighborhood)
    await finish_profile_edit(callback, state)

@router.message(StateFilter(UserStates.edit_neighborhood))
async def edit_neighborhood_text_handler(message: Message, state: FSMContext):
    if message.text:
        await db.update_user_field(message.from_user.id, "neighborhood", message.text)
    await finish_profile_edit(message, state)

@router.callback_query(F.data == "edit_phone")
async def edit_phone_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_phone)
    lang = await get_user_lang(callback.from_user.id)
    await callback.message.delete() # Matnli xabarga o'tish uchun eskisini o'chiramiz
    await callback.message.answer(get_text("enter_new_phone", lang), parse_mode="HTML", reply_markup=phone_keyboard(lang))
    await callback.answer()


@router.message(StateFilter(UserStates.edit_phone))
async def edit_phone_handler(message: Message, state: FSMContext):
    lang = await get_user_lang(message.from_user.id)
    
    if message.contact:
        phone = message.contact.phone_number
    elif message.text:
        phone = message.text.strip()
    else:
        await message.reply(get_text("enter_new_phone", lang), reply_markup=phone_keyboard(lang))
        return

    clean_phone = re.sub(r'[^\d+]', '', phone)
    
    if clean_phone.isdigit():
        if len(clean_phone) == 9:
             formatted_phone = f"+998{clean_phone}"
        elif len(clean_phone) == 12 and clean_phone.startswith("998"):
             formatted_phone = f"+{clean_phone}"
        else:
             formatted_phone = f"+{clean_phone}"
    else:
        formatted_phone = clean_phone

    digits_only = re.sub(r'\D', '', formatted_phone)
    if len(digits_only) < 7 or len(digits_only) > 15:
        await message.reply("⚠️ Iltimos, to'g'ri telefon raqam kiriting.", reply_markup=phone_keyboard(lang))
        return

    await db.update_user_field(message.from_user.id, "phone", formatted_phone)
    await finish_profile_edit(message, state)

@router.callback_query(F.data == "edit_location")
async def edit_location_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.edit_location)
    lang = await get_user_lang(callback.from_user.id) # noqa
    await callback.message.delete()
    await callback.message.answer(get_text("enter_new_location", lang), parse_mode="HTML", reply_markup=location_keyboard(lang))
    await callback.answer()


@router.message(StateFilter(UserStates.edit_location), F.content_type == ContentType.LOCATION)
async def edit_location_handler(message: Message, state: FSMContext):
    if message.location:
        loc = f"{message.location.latitude},{message.location.longitude}"
        await db.update_user_field(message.from_user.id, "location", loc)
    await finish_profile_edit(message, state)

@router.message(StateFilter(UserStates.edit_location))
async def edit_location_text_handler(message: Message, state: FSMContext):
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await go_to_main_menu(message, state)
        return
    lang = await get_user_lang(message.from_user.id)
    await message.answer(get_text("enter_new_location", lang), reply_markup=location_keyboard(lang))


# --- Profil o'chirish ---
@router.callback_query(F.data == "delete_profile")
async def delete_profile_callback(callback: CallbackQuery, state: FSMContext):
    await state.set_state(UserStates.confirm_delete)
    lang = await get_user_lang(callback.from_user.id)
    kb = confirm_delete_keyboard(lang)
    text = get_text("confirm_delete_profile", lang)
    
    # Agar xabar rasm bo'lsa (profil rasmi), uni o'chirib matn yuboramiz
    await safe_edit_message(callback, text, reply_markup=kb)
        
    await callback.answer("O'chirish tasdiqlash! ⚠️")


@router.callback_query(StateFilter(UserStates.confirm_delete), F.data == "confirm_delete_yes")
async def confirm_delete_yes(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    await db.delete_user_profile(user_id)
    await clear_state_preserve_session(state)

    lang = await get_user_lang(user_id)

    await callback.answer(get_text("profile_deleted", lang))
    await callback.message.edit_text(get_text("profile_deleted", lang), reply_markup=await profile_keyboard(False, lang, user_id))


@router.callback_query(StateFilter(UserStates.confirm_delete), F.data == "confirm_delete_no")
async def confirm_delete_no(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    
    # Sharh: Profil ma'lumotlarini qayta yuklash
    user = await db.get_user(user_id)
    profile_text = await get_user_profile_text(user, lang)
    
    await callback.answer(get_text("action_cancelled", lang))
    # Sharh: Bekor qilinganda profilni qayta ko'rsatish va link preview'ni o'chirish
    await callback.message.edit_text(
        profile_text, 
        parse_mode="HTML", 
        reply_markup=await profile_keyboard(has_profile=True, lang=lang, user_id=user_id),
        disable_web_page_preview=True
    )


@router.callback_query(F.data == "restore_profile")
async def restore_profile_callback(callback: CallbackQuery):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    if await db.restore_user_profile(user_id):
        user = await db.get_user(user_id)
        profile_text = await get_user_profile_text(user, lang)
        await callback.answer("Profil tiklab olindi! ✅")
        # Tarjima qilingan matnni ishlatish
        await callback.message.edit_text(
            f"{get_text('profile_restored_success', lang)}\n\n{profile_text}",
            parse_mode="HTML",
            reply_markup=await profile_keyboard(True, lang),
            disable_web_page_preview=True
        )
    else:
        await callback.answer("Tiklash uchun backup topilmadi! ⚠️", show_alert=True)


# ============================================================
# Qo'llab-quvvatlash (Support)
# ============================================================
@router.callback_query(F.data == "menu_support")
async def support_handler(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)

    if not await db.has_profile(user_id) and not await is_user_admin(user_id):
        await callback.message.edit_text("Avval profilni to'ldiring! 👤", reply_markup=await profile_keyboard(has_profile=False))
        return

    if await db.get_active_admin(user_id) is not None:
        await callback.message.edit_text("Siz allaqachoy chatdasiz. 💬", reply_markup=support_active_keyboard(lang))
        return

    if await db.is_pending_support(user_id):
        await callback.message.edit_text(get_text("support_request_sent", lang), reply_markup=support_waiting_keyboard(lang))
        return

    await db.set_pending_support(user_id, True)
    await state.set_state(UserStates.support_chat)
    await callback.message.edit_text(get_text("support_request_sent", lang), reply_markup=support_waiting_keyboard(lang))

    # Adminga xabar yoborish
    user_data = await db.get_user(user_id)
    profile_text = await get_user_profile_text(user_data, lang, for_admin=True)
    username = callback.from_user.username or "noma'lum"

    if not ADMIN_IDS:
        logger.error("ADMIN_IDS bo'sh! .env faylini tekshiring.")
        await callback.message.answer("Texnik xato: Adminlar topilmadi. Keyinroq urinib ko'ring.")
        await db.set_pending_support(user_id, False)
        await clear_state_preserve_session(state)
        return

    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(
                admin_id,
                f"🆘 <b>Yangi muloqot so'rovi!</b>\n\n"
                f"Foydalanuvchi ID: <code>{user_id}</code> (@{username})\n\n"
                f"{profile_text}\n\n"
                f"👇 Tasdiqlash yoki bekor qilish:",
                parse_mode="HTML",
                disable_web_page_preview=True,
                reply_markup=support_accept_keyboard(user_id),
            )
        except Exception as e:
            logger.error("Adminga xabar yuborishda xato: %s", e)


@router.callback_query(lambda c: c.data.startswith("accept_support_"))
async def accept_support_callback(callback: CallbackQuery, bot: Bot):
    user_id = int(callback.data.split("_")[2])
    admin_id = callback.from_user.id
    lang = await get_user_lang(user_id)

    if await db.get_active_admin(user_id) is None and await db.is_pending_support(user_id):
        await db.set_pending_support(user_id, False)
        await db.set_active_chat(user_id, admin_id)
        await db.log_action("Support Start", user_id, f"Admin: {admin_id}")
        await callback.answer("Chat qabul qilindi! ✅")

        try:
            await callback.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass

        end_kb = InlineKeyboardBuilder()
        end_kb.add(InlineKeyboardButton(text="🔚 Chatni yakunlash", callback_data=f"admin_end_chat_{user_id}"))
        await callback.message.answer(
            "Chat faollashtirildi! 💬\nFoydalanuvchi bilan suhbatlashish mumkin.\nYakunlash uchun tugmani bosing 👇",
            reply_markup=end_kb.as_markup(),
        )

        try:
            await bot.send_message(
                user_id,
                get_text("admin_joined_chat", lang),
                reply_markup=support_active_keyboard(lang),
            )
        except Exception as e:
            logger.error("Foydalanuvchiga xabar yuborishda xato: %s", e)
    else:
        await callback.answer("So'rov allaqachon ishlov berilgan. ⚠️")
@router.callback_query(F.data.startswith("reject_support_"))
async def reject_support_callback(callback: CallbackQuery, bot: Bot):
    user_id = int(callback.data.split("_")[2])
    lang = await get_user_lang(user_id)

    if await db.is_pending_support(user_id):
        await db.set_pending_support(user_id, False)
        await callback.answer("So'rov rad etildi! ❌")
        try:
            await callback.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
        try:
            await bot.send_message(user_id, get_text("admin_rejected_chat", lang), reply_markup=main_menu_keyboard(lang=lang))
        except Exception as e:
            logger.error("Foydalanuvchiga xabar yuborishda xato: %s", e)
    else:
        await callback.answer("So'rov allaqachon ishlov berilgan. ⚠️")


@router.message(StateFilter(UserStates.support_chat))
async def user_support_message(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    lang = await get_user_lang(user_id)

    if message.text in ("❌ Chatni yakunlash", "🏠 Bosh menyuga"):
        # Agar reply keyboard qolgan bo'lsa, uni ushlash uchun
        admin_id = await db.get_active_admin(user_id)
        if admin_id:
            try:
                await bot.send_message(admin_id, get_text("chat_ended_user", lang))
            except Exception as e:
                logger.error(f"Adminga chat yakunlangani haqida yuborishda xato: {e}")
            await db.remove_active_chat(user_id)

        await clear_state_preserve_session(state)
        await message.answer(get_text("rate_bot", lang), reply_markup=rating_keyboard())
        return

    admin_id = await db.get_active_admin(user_id)
    if admin_id:
        username = message.from_user.username or "noma'lum"
        try:
            await bot.send_message(admin_id, f"Foydalanuvchidan {user_id} (@{username}): {escape(message.text)}", parse_mode="HTML")
            await message.answer(get_text("msg_wait_admin", lang))
        except Exception as e:
            logger.error("Adminga xabar yuborishda xato: %s", e)
            await message.reply("Xabar yuborishda xato. Iltiros, qayta urinib ko'ring.")
    else:
        await message.reply("Chat faol emas. ⚠️")

@router.callback_query(F.data == "support_cancel")
async def support_cancel_callback(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    await db.set_pending_support(user_id, False)
    # go_to_main_menu o'zi clear qiladi, lekin preserve qilish kerak
    await go_to_main_menu(callback, state)


@router.callback_query(F.data == "support_end")
async def support_end_callback(callback: CallbackQuery, bot: Bot, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    admin_id = await db.get_active_admin(user_id)
    if admin_id:
        try:
            await bot.send_message(admin_id, get_text("chat_ended_user", lang))
        except Exception:
            pass
        await db.remove_active_chat(user_id)
        await db.log_action("Support End", user_id, "User ended")
    await state.clear()
    await callback.message.edit_text(get_text("chat_ended_rate", lang), reply_markup=rating_keyboard())


@router.callback_query(F.data.startswith("admin_end_chat_"))
async def admin_end_chat_callback(callback: CallbackQuery, bot: Bot):
    user_id = int(callback.data.split("_")[3])
    admin_id = callback.from_user.id
    lang = await get_user_lang(admin_id)

    if await db.get_active_admin(user_id) == admin_id:
        await db.remove_active_chat(user_id)
        await db.log_action("Support End", user_id, f"Admin {admin_id} ended")
        await callback.answer("Chat yakunlandi! ✅")
        try:
            await callback.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
        
        # Adminga menyuni qaytarish
        await callback.message.answer("Chat yakunlandi. Admin panel:", reply_markup=admin_keyboard(lang))
        
        try:
            await bot.send_message(
                user_id,
                "Admin chatni yakunladi. ❌\n\nXizmatimiz sizga yoqdimi? 😊",
                reply_markup=like_keyboard(),
            )
        except Exception as e:
            logger.error("Foydalanuvchiga xabar yuborishda xato: %s", e)


@router.message(
    lambda m: (
        m.from_user.id in ADMIN_IDS
        and m.reply_to_message is not None
        and m.reply_to_message.text is not None
        and "Foydalanuvchidan" in m.reply_to_message.text
    )
)
async def admin_reply_handler(message: Message, bot: Bot):
    try:
        # "Foydalanuvchidan 12345 (@user): ..."
        after = message.reply_to_message.text.split("Foydalanuvchidan")[1]
        user_id = int(after.strip().split()[0]) # noqa
        if await db.get_active_admin(user_id) == message.from_user.id:
            lang = await get_user_lang(user_id)
            await bot.send_message(user_id, f"Admindan: {escape(message.text)}", reply_markup=support_active_keyboard(lang), parse_mode="HTML")
            await message.reply("Xabaringiz foydalanuvchiga yuborildi, javobni kuting. ⏳")
    except (ValueError, IndexError) as e:
        logger.error("Admin javob parselanayotganda xato: %s", e)


# ============================================================
# Shikoyat yuborish (Banned Users)
# ============================================================
@router.callback_query(F.data == "send_complaint")
async def send_complaint_handler(callback: CallbackQuery, state: FSMContext):
    """Bloklangan foydalanuvchi 'Shikoyat yuborish' tugmasini bosganda ishlaydi."""
    user_id = callback.from_user.id
    user = await db.get_user(user_id)

    # Faqat bloklangan foydalanuvchilar uchun qo'shimcha tekshiruv
    if not (user and user[10] == 1):
        await callback.answer("Bu funksiya faqat bloklangan foydalanuvchilar uchun.", show_alert=True)
        return

    await state.set_state(UserStates.complaint)
    try:
        # Eski xabardagi tugmalarni olib tashlash
        await callback.message.edit_reply_markup(reply_markup=None)
    except Exception:
        pass
    await callback.message.answer(
        "Iltimos shikoyatingizni yozib qoldiring, men uni ko'rib chiqish uchun yuboraman."
    )
    await callback.answer()


@router.message(StateFilter(UserStates.complaint))
async def complaint_receive_handler(message: Message, state: FSMContext, bot: Bot):
    """Bloklangan foydalanuvchidan kelgan shikoyat matnini qabul qiladi."""
    user_id = message.from_user.id
    user = await db.get_user(user_id)

    # Yana bir bor tekshiruv
    if not (user and user[10] == 1):
        await clear_state_preserve_session(state)
        return
    await db.update_user_field(user_id, "complaint_sent", 1) # Shikoyat yuborilganini belgilash

    complaint_text = message.text
    lang = await get_user_lang(user_id)
    profile_text = await get_user_profile_text(user, lang)
    username = message.from_user.username or "noma'lum"

    # Adminga shikoyatni yuborish
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(
                admin_id,
                f"‼️ <b>Bloklangan foydalanuvchidan shikoyat!</b>\n\nID: <code>{user_id}</code> (@{username})\n\n👤 <b>Profil:</b>\n{profile_text}\n\n💬 <b>Matn:</b>\n{escape(str(complaint_text))}",
                parse_mode="HTML",
            )
        except Exception as e:
            logger.error(f"Adminga shikoyat yuborishda xato: {e}")

    await clear_state_preserve_session(state)
    await message.answer(
        "Shikoyatingiz yuborildi, iltimos kuting. Biz tekshirib chiqib, hisobingizdagi barcha cheklovlarini olib tashlaymiz."
    )

@router.message(Command("yakunlash"), lambda m: m.from_user.id in ADMIN_IDS)
async def admin_end_chat_command(message: Message, bot: Bot):
    if (
        message.reply_to_message
        and message.reply_to_message.text
        and "Foydalanuvchidan" in message.reply_to_message.text
    ):
        try:
            after = message.reply_to_message.text.split("Foydalanuvchidan")[1]
            user_id = int(after.strip().split()[0])
            if await db.get_active_admin(user_id) == message.from_user.id:
                await db.log_action("Support End", user_id, f"Admin {message.from_user.id} ended (command)")
                try:
                    await bot.send_message(
                        user_id,
                        "Admin chatni yakunladi. ❌\nXizmatimiz sizga yoqdimi? 😊",
                        reply_markup=like_keyboard(),
                    )
                except Exception as e:
                    logger.error("Foydalanuvchiga xabar yuborishda xato: %s", e)
                await message.reply("Chat yakunlandi. ❌")
        except (ValueError, IndexError) as e:
            logger.error("Yakunlash komandasi parselanayotganda xato: %s", e)


# ============================================================
# Fikr bildirish (Feedback)
# ============================================================
@router.callback_query(F.data == "menu_feedback")
async def feedback_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id    
    if not await db.has_profile(user_id) and not await is_user_admin(user_id):
        await callback.message.edit_text("Avval profilni to'ldiring! 👤", reply_markup=await profile_keyboard(has_profile=False))
        return

    await state.set_state(UserStates.feedback)
    lang = await get_user_lang(user_id)
    await callback.message.edit_text(get_text("feedback_welcome_name", lang, name=callback.from_user.first_name), reply_markup=cancel_keyboard(lang))


@router.message(StateFilter(UserStates.feedback))
async def feedback_send(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    username = message.from_user.username or "noma'lum"
    user = await db.get_user(user_id)
    lang = await get_user_lang(user_id)
    
    # Matn yoki caption
    feedback_content = message.text or message.caption or "Fayl (Rasm/Video/Audio)"
    await db.log_action("Feedback", user_id, feedback_content)
    
    # Admin uchun formatlash
    profile_text = await get_user_profile_text(user, lang, for_admin=True)
    full_message_text = f"📩 <b>Yangi fikr/taklif!</b>\n\n👤 <b>Foydalanuvchi:</b> {user_id} (@{username})\n\n{profile_text}\n\n📝 <b>Fikr:</b>\n{escape(feedback_content)}"

    for admin_id in ADMIN_IDS:
        try:
            # Bitta xabar sifatida yuborish (Matn bo'lsa)
            if message.text:
                await bot.send_message(
                    admin_id,
                    full_message_text,
                    parse_mode="HTML",
                    disable_web_page_preview=True
                )
            else:
                # Media bo'lsa (Rasm/Video) caption bilan yoki alohida
                # Agar caption sig'sa, rasmga qo'shamiz
                if len(full_message_text) < 1000:
                     await message.copy_to(chat_id=admin_id, caption=full_message_text, parse_mode="HTML")
                else:
                     # Sig'masa alohida
                     await bot.send_message(admin_id, full_message_text, parse_mode="HTML")
                     await message.copy_to(chat_id=admin_id)
                     
        except Exception as e:
            logger.error("Adminga fikr yuborishda xato: %s", e)

    # Foydalanuvchi ismini olish
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else message.from_user.first_name

    await state.clear()
    is_admin = await is_user_admin(user_id)
    await message.answer(get_text("feedback_received_return_main", lang, name=display_name), reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name))


# --- Like / Rating / Comment (chat yakunlash keyingi flow) ---
@router.callback_query(F.data.startswith("like_"))
async def like_feedback_callback(callback: CallbackQuery, state: FSMContext):
    liked = 1 if callback.data == "like_yes" else 0
    user_id = callback.from_user.id
    await state.set_state(UserStates.rating_feedback)

    liked_text = "Ha!" if liked else "Yo'q!"
    await callback.message.edit_text(
        f"Rahmat! {liked_text}\n\nIltiros, baholang (1–5 yulduz): ⭐",
        reply_markup=rating_keyboard(),
    )
    await callback.answer("Baholashni davom ettir! ⭐")


@router.callback_query(F.data.startswith("rating_"))
async def rating_feedback_callback(callback: CallbackQuery, state: FSMContext):
    rating = int(callback.data.split("_")[1])
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await db.save_feedback(user_id, rating=rating)
    await state.set_state(UserStates.comment_feedback)
    
    await callback.message.edit_text(
        get_text("write_feedback", lang),
        reply_markup=cancel_keyboard(lang),
    )
    await callback.answer(f"Rahmat! {rating} ⭐")


@router.message(StateFilter(UserStates.comment_feedback))
async def comment_feedback_handler(message: Message, bot: Bot, state: FSMContext):
    user_id = message.from_user.id
    await db.save_feedback(user_id, comment=message.text)

    # Feedback ma'lumotlarini adminga yuborish
    user = await db.get_user(user_id)
    lang = await get_user_lang(user_id)
    profile_text = await get_user_profile_text(user, lang)
    username = message.from_user.username or "noma'lum"

    # Foydalanuvchi ismini olish
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else message.from_user.first_name

    await clear_state_preserve_session(state)
    is_admin = await is_user_admin(user_id)
    lang = await get_user_lang(user_id)
    await message.answer(get_text("feedback_thank_you_full", lang), reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name))
    
    # Ensure state is cleared to prevent freezing
    # await state.clear() - Yuqorida bajarildi
    # Log success
    logger.info(f"Feedback received from {user_id}")

# ============================================================
# Buyurtmalar (Orders)
# ============================================================
@router.message(StateFilter(UserStates.order))
async def order_handler(message: Message, state: FSMContext, bot: Bot):
    user_id = message.from_user.id
    order_id = await db.add_order(user_id, message.text)
    await db.log_action("Order", user_id, f"Order #{order_id}: {message.text}")
    await clear_state_preserve_session(state)
    
    # Foydalanuvchi ismini olish
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else message.from_user.first_name

    is_admin = await is_user_admin(user_id)
    lang = await get_user_lang(user_id)
    await message.answer("Buyurtma qabul qilindi! ⏳", reply_markup=main_menu_keyboard(is_admin=is_admin, lang=lang, user_name=display_name))

    username = message.from_user.username or "noma'lum"
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(
                admin_id,
                f"Yangi buyurtma #{order_id} foydalanuvchidan {user_id} (@{username}): {message.text}",
                disable_web_page_preview=True,
                reply_markup=order_actions_keyboard(order_id),
            )
        except Exception as e:
            logger.error("Adminga buyurtma yuborishda xato: %s", e)


@router.callback_query(F.data.startswith("order_"))
async def order_action_callback(callback: CallbackQuery, bot: Bot):
    parts = callback.data.split("_")
    if len(parts) < 3:
        await callback.answer("Xato! Noto'g'ri format.")
        return

    action = parts[1]
    order_id = int(parts[2])

    STATUS_MAP = {"complete": "bajarildi", "later": "keyinroq", "cancel": "bekor qilindi"}
    status = STATUS_MAP.get(action)
    if not status:
        await callback.answer("Noma'lum harakat!")
        return
    
    await db.update_order_status(order_id, status)
    order = await db.get_order(order_id)

    if order:
        user_id = order[1]
        try:
            lang = await get_user_lang(user_id)
            if action == "complete":
                await bot.send_message(user_id, get_text("order_status_completed_msg", lang))
            elif action == "later":
                await bot.send_message(user_id, get_text("order_status_later_msg", lang))
                
        except Exception as e:
            logger.error("Foydalanuvchiga buyurtma statusi yuborishda xato: %s", e)

    await callback.answer(f"Status o'zgartirildi: {status}")
    try:
        await callback.message.edit_text(callback.message.text + f"\n\n✅ Yangilangan status: {status}")
    except Exception:
        pass


# ============================================================
# Bot haqida
# ============================================================
@router.callback_query(F.data == "menu_about")
async def about_bot_handler(callback: CallbackQuery):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    text = get_text("about_text", lang)

    # O'zgarish: "Bot haqida" bo'limiga "Video qo'llanma" tugmasini qo'shish
    builder = InlineKeyboardBuilder()

    # Video qo'llanma mavjudligini bazadan tekshirish
    video_guide_file_id = await db.get_setting('video_guide_file_id')
    if video_guide_file_id:
        builder.add(InlineKeyboardButton(text=get_text("video_guide_btn", lang), callback_data="show_video_guide"))

    builder.add(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(1)

    await callback.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())


@router.callback_query(F.data == "show_video_guide")
async def show_video_guide_handler(callback: CallbackQuery, bot: Bot):
    """Foydalanuvchiga video qo'llanmani yuborish uchun handler"""
    video_guide_file_id = await db.get_setting('video_guide_file_id')
    if video_guide_file_id:
        await callback.answer()
        await bot.send_video(callback.from_user.id, video_guide_file_id, caption="Botdan foydalanish bo'yicha video qo'llanma.")
    else:
        await callback.answer(get_text("no_guide_available", await get_user_lang(callback.from_user.id)), show_alert=True)


# ============================================================
# Admin Panel
# ============================================================
@router.callback_query(F.data == "admin_panel")
async def admin_panel_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):
        # Xavfsizlik: Ruxsatsiz urinish haqida asosiy adminga xabar
        if ADMIN_IDS:
            try:
                username = callback.from_user.username or "No username"
                await callback.bot.send_message(ADMIN_IDS[0], f"⚠️ <b>Xavfsizlik ogohlantirishi!</b>\nFoydalanuvchi {callback.from_user.id} (@{username}) admin panelga kirishga urindi!", parse_mode="HTML")
            except: pass
            
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    await callback.message.edit_text(get_text("admin_welcome", lang), reply_markup=admin_keyboard(lang)) # noqa

@router.callback_query(F.data == "admin_data")
async def admin_data_handler(callback: CallbackQuery):
    """
    Admin panelidagi "📂 Ma'lumotlar" tugmasi uchun handler.
    Bu tugma bosilganda, ma'lumotlar bilan bog'liq bo'lgan boshqa menyu (statistika, foydalanuvchilar, guruhlar) ochiladi.
    """
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    lang = 'uz'

    # Sharh: Agar oldingi xabar rasm bo'lsa (masalan, statistika grafigi),
    # uni tahrirlab bo'lmaydi. Shuning uchun xatoni ushlab, eski xabarni o'chirib,
    # yangisini yuboramiz. Bu usul botning har qanday holatda ham to'g'ri ishlashini ta'minlaydi.
    await safe_edit_message(callback, "📂 Ma'lumotlar bo'limi", reply_markup=data_menu_keyboard(lang))

@router.callback_query(F.data == "admin_banned")
async def banned_handler(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    lang = 'uz'

    banned_users = await db.get_banned_users()
    if not banned_users:
        await callback.message.edit_text("Bloklangan foydalanuvchilar yo'q.", reply_markup=back_to_admin_keyboard())
        return

    mapping = {}
    text = "🚫 <b>Bloklangan foydalanuvchilar:</b>\n\n"
    for idx, user in enumerate(banned_users, 1):
        mapping[idx] = user[0] # noqa
        username = f"@{user[1]}" if user[1] else get_text('lbl_none', lang)
        full_name = (user[4] if len(user) > 4 and user[4] else get_text('lbl_none', lang))
        text += (
            f"{idx}. ID: {user[0]}\n"
            f"Username: {username}\n"
            f"To'liq ism: {full_name}\n"
            f"{'─' * 30}\n"
        )
 # noqa
    await state.update_data(banned_mapping=mapping)
    await state.set_state(AdminStates.banned_selection)

    text += "\nBlokdan chiqarish uchun tartib raqamini yuboring (masalan: 1):"

    if len(text) > 4096:
        await callback.message.delete()
        for i in range(0, len(text), 4096):
            chunk = text[i : i + 4096]
            markup = back_to_admin_keyboard() if (i + 4096 >= len(text)) else None
            await callback.message.answer(chunk, parse_mode="HTML", reply_markup=markup) # noqa
    else: # noqa
        await callback.message.edit_text(text, parse_mode="HTML", reply_markup=back_to_admin_keyboard())


@router.message(StateFilter(AdminStates.banned_selection))
async def admin_unblock_selection(message: Message, state: FSMContext):
    lang = 'uz'
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await state.clear()
        await message.answer("Bekor qilindi.", reply_markup=admin_keyboard(lang))
        return

    data = await state.get_data()
    mapping = data.get("banned_mapping", {})
    
    try:
        selection = int(message.text)
        user_id = mapping.get(selection)
        if user_id:
            # Tasdiqlashni so'rash
            await state.update_data(unblock_user_id=user_id)
            await state.set_state(AdminStates.confirm_unblock)
            await message.answer(f"Haqiqatdan ham foydalanuvchi {user_id} ni blokdan chiqarmoqchimisiz?", reply_markup=confirm_unblock_keyboard(lang))
        else:
            await message.answer("Noto'g'ri raqam! Qayta urinib ko'ring.")
    except ValueError:
        await message.answer("Iltimos, raqam kiriting.")

@router.callback_query(StateFilter(AdminStates.confirm_unblock), F.data == "confirm_unblock_yes")
async def admin_confirm_unblock_yes(callback: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    user_id = data.get("unblock_user_id")
    
    if user_id:
        await db.update_user_field(user_id, "is_banned", 0)
        await callback.message.edit_text(f"Foydalanuvchi {user_id} blokdan chiqarildi! ✅", reply_markup=back_to_admin_keyboard())
        try:
            await callback.bot.send_message(user_id, "Siz blokdan chiqarildingiz! ✅\nBotdan qayta foydalanishingiz mumkin.") # noqa
        except: pass
    else:
        await callback.message.edit_text("Xatolik yuz berdi.", reply_markup=back_to_admin_keyboard())

    await clear_state_preserve_session(state)

@router.callback_query(StateFilter(AdminStates.confirm_unblock), F.data == "confirm_unblock_no")
async def admin_confirm_unblock_no(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    # Qayta ro'yxatni ko'rsatish uchun banned_handler ga o'xshash logika kerak yoki shunchaki menyuga qaytish
    # Oddiylik uchun menyuga qaytamiz
    await callback.message.edit_text("Bekor qilindi.", reply_markup=back_to_admin_keyboard())

def stats_period_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("stats_daily", lang), callback_data="stats_period_daily"))
    builder.add(InlineKeyboardButton(text=get_text("stats_weekly", lang), callback_data="stats_period_weekly"))
    builder.add(InlineKeyboardButton(text=get_text("stats_monthly", lang), callback_data="stats_period_monthly"))
    builder.row(InlineKeyboardButton(text="⬅️ Orqaga", callback_data="admin_data"))
    return builder.as_markup()


@router.callback_query(F.data == "admin_stats") # noqa
async def stats_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    await callback.message.edit_text(get_text("admin_stats_menu", lang), reply_markup=stats_period_keyboard(lang))


@router.callback_query(lambda c: c.data.startswith("stats_period_"))
async def show_stats_period_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):
        return

    period = callback.data.split('_')[-1]
    stats = await db.get_stats()
    total, banned = stats["total"], stats["banned"]
    active = total - banned

    if period == "daily":
        new_users = stats["new_today"]
        downloads = stats["dl_today"]
        period_text = "Bugun"
    elif period == "weekly":
        new_users = stats["new_week"]
        downloads = stats["dl_week"]
        period_text = "Shu hafta"
    else:  # monthly
        new_users = stats["new_month"]
        downloads = stats["dl_month"]
        period_text = "Shu oy"

    active_bar = make_progress_bar(active, total)
    banned_bar = make_progress_bar(banned, total)
    active_pct = (active / total * 100) if total > 0 else 0
    banned_pct = (banned / total * 100) if total > 0 else 0

    text_caption = (
        f"📊 <b>Statistika ({period_text})</b>\n\n"
        f"👥 <b>Jami foydalanuvchilar:</b> {total}\n\n"
        f"📅 <b>{period_text} qo'shilganlar:</b> {new_users}\n"
        f"📥 <b>{period_text} yuklashlar:</b> {downloads}\n\n"
        f"✅ <b>Faol:</b> {active} ({active_pct:.1f}%)\n{active_bar}\n\n"
        f"🚫 <b>Bloklangan:</b> {banned} ({banned_pct:.1f}%)\n{banned_bar}"
    )

    await safe_edit_message(callback, text_caption, reply_markup=stats_period_keyboard('uz'))
    
    await callback.answer()

@router.callback_query(F.data == "admin_broadcast")
async def broadcast_handler(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return

    await state.set_state(AdminStates.broadcast) # noqa
    lang = 'uz'
    await callback.message.edit_text(get_text("admin_broadcast_prompt", lang), reply_markup=cancel_keyboard(lang))


@router.message(StateFilter(AdminStates.broadcast))
async def broadcast_send(message: Message, state: FSMContext, bot: Bot):
    users = await db.get_all_users()
    sent_count = 0
    deleted_count = 0
    error_count = 0

    status_msg = await message.answer(f"📢 Elon yuborish boshlandi...\nJami: {len(users)} ta foydalanuvchi.")

    for i, user in enumerate(users):
        user_id = user[0] # noqa
        try:
            await message.copy_to(chat_id=user_id)
            sent_count += 1
            # Har 25 ta xabardan so'ng 1 soniya kutish (Telegram limitlariga tushmaslik uchun)
            if i > 0 and i % 25 == 0:
                await asyncio.sleep(1)
                try: # Admin uchun jarayon haqida xabar berish
                    await status_msg.edit_text(f"Jarayon: {i}/{len(users)}\n✅ Yuborildi: {sent_count}\n🗑 O'chirilgan: {deleted_count}")
                except TelegramBadRequest: pass # Xabar o'zgarmagan bo'lsa, e'tibor bermaymiz
        except TelegramForbiddenError: # Botni bloklagan
            deleted_count += 1
            await db.delete_user(user_id)
            logger.info(f"Foydalanuvchi {user_id} botni bloklagani uchun bazadan o'chirildi.")
        except TelegramBadRequest as e:
            if "chat not found" in str(e).lower():
                deleted_count += 1
                # O'chirilgan hisobni bazadan o'chiramiz
                await db.delete_user(user_id)
                logger.info(f"Foydalanuvchi {user_id} topilmagani (o'chirilgan) uchun bazadan o'chirildi.")
            else:
                error_count += 1
                logger.error(f"Foydalanuvchiga elon yuborishda kutilmagan xato ({user_id}): {e}")
        except Exception as e:
            error_count += 1
            logger.error(f"Foydalanuvchiga elon yuborishda umumiy xato ({user_id}): {e}")

    await clear_state_preserve_session(state)
    lang = 'uz'
    summary_text = (
        f"📢 <b>Elon yuborish yakunlandi!</b>\n"
        f"✅ Yuborildi: {sent_count} ta\n"
        f"🗑 Bloklagan/O'chirganlar: {deleted_count} ta\n"
        f"⚠️ Xatoliklar: {error_count} ta\n"
    )
    await status_msg.edit_text(summary_text, parse_mode="HTML", reply_markup=admin_keyboard(lang))

@router.callback_query(F.data == "admin_users")
async def users_handler(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    mapping = await show_users_page(callback, state, page=0)
    await state.update_data(user_mapping=mapping)
    await state.set_state(AdminStates.user_selection)

async def show_users_page(callback: CallbackQuery, state: FSMContext, page: int):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return

    # Admin panel faqat o'zbek tilida # noqa
    lang = 'uz' 
    
    # Foydalanuvchilar sonini va ro'yxatini olish
    total_users = await db.get_users_count() # noqa
    if total_users == 0:
        await callback.message.edit_text("Foydalanuvchilar yo'q.", reply_markup=admin_keyboard(lang))
        return

    ITEMS_PER_PAGE = 10 # Foydalanuvchi talabiga binoan 10 taga o'zgartirildi
    total_pages = (total_users + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
    start_idx = page * ITEMS_PER_PAGE
    # Bazadan faqat kerakli qismini olish (Optimallashtirish)
    current_users = await db.get_users_paginated(ITEMS_PER_PAGE, start_idx)
    
    # Save mapping for selection
    # Xabar matnini shakllantirish
    # Foydalanuvchilar ro'yxati uzun bo'lishi mumkin, shuning uchun uni qismlarga bo'lishimiz kerak
    # Yoki shunchaki birinchi xabarni tahrirlab, qolganini yangi xabar qilib yuborishimiz mumkin.
    # Hozircha, xabar uzunligini tekshirib, agar oshib ketsa, yangi xabar yuborishni qo'shamiz.
    
    # Birinchi qism: sarlavha va umumiy ma'lumot
    mapping = {}
    base_text = get_text("admin_users_count", lang, count=total_users) + get_text("admin_users_list", lang) + "\n\n"
    
    current_page_users_text = ""
    
    for idx, user in enumerate(current_users, 1):
        real_idx = idx  # 1 to 5
        mapping[real_idx] = user[0]

        # Foydalanuvchi onlayn statusini tekshirish
        # `last_active` ustuni indeksi 14
        last_active_iso = user[14] if len(user) > 14 else None
        is_online = "🔴" # Offline
        if last_active_iso:
            try:
                last_active_dt = datetime.fromisoformat(last_active_iso)
                if (datetime.now() - last_active_dt).total_seconds() < 300: # 5 daqiqa
                    is_online = "🟢" # Online
            except:
                pass

        username = f"@{user[1]}" if user[1] else "Yo'q"
        # Foydalanuvchi ismini HTML dan himoyalash
        tg_name = f"{escape(user[2] or '')} {escape(user[3] or '')}".strip() or "Ism yo'q"
        current_page_users_text += f"<b>{real_idx}.</b> {is_online} {tg_name} ({username}) [ID: {user[0]}]\n"
    
    builder = InlineKeyboardBuilder()
    # Navigatsiya tugmalari
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton(text="⬅️ Oldingi", callback_data=f"admin_users_page_{page-1}"))
    
    nav_row.append(InlineKeyboardButton(text=f"📄 {page+1}/{total_pages}", callback_data="noop")) # Sahifa

    if (page + 1) < total_pages:
        nav_row.append(InlineKeyboardButton(text="Keyingi ➡️", callback_data=f"admin_users_page_{page+1}"))
    
    builder.row(*nav_row)
    
    # Excel tugmasi shu yerga qo'shildi
    builder.row(InlineKeyboardButton(text=get_text("users_excel_btn", lang), callback_data="admin_export_excel"))
    builder.row(InlineKeyboardButton(text=get_text("refresh_btn", lang), callback_data=f"admin_users_page_{page}"))
    builder.row(InlineKeyboardButton(text=get_text("admin_back", lang), callback_data="admin_panel"))

    final_text = base_text + current_page_users_text
    
    if len(final_text) > 4096:
        # Agar xabar juda uzun bo'lsa, uni bo'lib yuboramiz
        await callback.message.edit_text(base_text, parse_mode="HTML")
        for i in range(0, len(current_page_users_text), 4000): # 4000 belgidan kichikroq qismlarga bo'lish
            chunk = current_page_users_text[i:i+4000]
            await callback.message.answer(chunk, parse_mode="HTML", reply_markup=builder.as_markup() if i + 4000 >= len(current_page_users_text) else None)
    else:
        await safe_edit_message(callback, final_text, reply_markup=builder.as_markup())

    # Foydalanuvchidan tanlovni kutish uchun prompt
    # await callback.message.answer("Boshqarish uchun foydalanuvchi raqamini yuboring:")

    return mapping

@router.callback_query(F.data.startswith("admin_users_page_"))
async def admin_users_pagination(callback: CallbackQuery, state: FSMContext):
    page = int(callback.data.split("_")[3])
    mapping = await show_users_page(callback, state, page)
    await state.update_data(user_mapping=mapping)
    await state.set_state(AdminStates.user_selection)

# ============================================================
# Admin Kanallar Boshqaruvi
# ============================================================
@router.callback_query(F.data == "admin_channels")
async def admin_channels_handler(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    
    channels = await db.get_channels()
    text = "📢 <b>Majburiy obuna kanallari:</b>\n\n"
    
    builder = InlineKeyboardBuilder()
    
    if not channels:
        text += "Hozircha kanallar yo'q."
        if CHANNEL_LINKS:
            text += "\n<i>(.env faylidan o'qilmoqda)</i>"
    else:
        for ch in channels:
            ch_id, ch_link = ch
            text += f"🔗 {ch_link}\n"
            builder.add(InlineKeyboardButton(text=f"🗑 O'chirish: {ch_link}", callback_data=f"admin_del_channel_{ch_id}"))
    
    builder.adjust(1)
    builder.row(InlineKeyboardButton(text="➕ Kanal qo'shish", callback_data="admin_add_channel"))
    builder.row(InlineKeyboardButton(text="⬅️ Admin panelga", callback_data="admin_panel"))
    
    await callback.message.edit_text(text, parse_mode="HTML", reply_markup=builder.as_markup())

@router.callback_query(F.data == "admin_add_channel")
async def admin_add_channel_start(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id):
        return
    await state.set_state(AdminStates.add_channel)
    await callback.message.edit_text(
        "Kanal linkini yoki ID sini yuboring:\n(Masalan: @kanal_nomi yoki -1001234567890)",
        reply_markup=back_to_admin_keyboard()
    )

@router.message(StateFilter(AdminStates.add_channel))
async def admin_add_channel_save(message: Message, state: FSMContext):
    if not await is_user_admin(message.from_user.id):
        return
    link = message.text.strip()
    # Sharh: Endi istalgan havolani qo'shish mumkin (youtube, instagram va hokazo)
    # Tekshiruv olib tashlandi. # noqa
    lang = 'uz'
    if await db.add_channel(link):
        await message.answer(f"✅ Kanal qo'shildi: {link}", reply_markup=admin_keyboard(lang))
    else:
        await message.answer("⚠️ Bu kanal allaqachon mavjud!", reply_markup=admin_keyboard(lang))
    
    await state.clear()

@router.callback_query(F.data.startswith("admin_del_channel_"))
async def admin_delete_channel(callback: CallbackQuery):
    ch_id = int(callback.data.split("_")[3])
    await db.delete_channel(ch_id)
    await callback.answer("Kanal o'chirildi! 🗑")
    # Ro'yxatni yangilash
    await admin_channels_handler(callback, None)

# ============================================================
# Admin Video Qo'llanma Boshqaruvi
# ============================================================

async def admin_video_guide_keyboard(lang: str = 'uz'):
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("upload_guide_btn", lang), callback_data="admin_upload_guide"))
    # Agar qo'llanma mavjud bo'lsa, o'chirish tugmasini ko'rsatish
    if await db.get_setting('video_guide_file_id'):
        builder.add(InlineKeyboardButton(text=get_text("delete_guide_btn", lang), callback_data="admin_delete_guide_ask"))
    builder.add(InlineKeyboardButton(text="⬅️ Admin panelga", callback_data="admin_panel"))
    builder.adjust(1)
    return builder.as_markup()

@router.callback_query(F.data == "admin_video_guide")
async def admin_video_guide_menu_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    await callback.message.edit_text(
        get_text("admin_video_guide_menu", lang),
        reply_markup=await admin_video_guide_keyboard(lang)
    )

@router.callback_query(F.data == "admin_upload_guide")
async def admin_upload_guide_start(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id): return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    await state.set_state(AdminStates.upload_video_guide)
    await callback.message.edit_text(get_text("send_video_guide_prompt", lang), reply_markup=back_to_admin_keyboard())

@router.message(StateFilter(AdminStates.upload_video_guide), F.content_type == ContentType.VIDEO)
# O'zgarish: ContentType.DOCUMENT ham qo'shildi, chunki Telegram ba'zan videolarni hujjat sifatida yuboradi.
@router.message(StateFilter(AdminStates.upload_video_guide), F.content_type.in_([ContentType.VIDEO, ContentType.DOCUMENT]))
async def admin_upload_guide_process(message: Message, state: FSMContext):
    if not await is_user_admin(message.from_user.id): return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    file_id = None
    if message.video:
        file_id = message.video.file_id
    elif message.document and message.document.mime_type and message.document.mime_type.startswith('video/'):
        file_id = message.document.file_id
    
    if file_id:
        logger.info(f"Admin video guide file_id received: {file_id}")
        await db.set_setting('video_guide_file_id', file_id)
        await clear_state_preserve_session(state)
        await message.answer(get_text("guide_uploaded_success", lang), reply_markup=admin_keyboard(lang))
    else:
        await message.answer("Iltimos, video fayl yuboring (yoki video sifatida yuborilgan hujjat).", reply_markup=admin_keyboard(lang))

@router.callback_query(F.data == "admin_delete_guide_ask")
async def admin_delete_guide_ask_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id): return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("yes", lang), callback_data="admin_delete_guide_confirm"))
    builder.add(InlineKeyboardButton(text=get_text("no", lang), callback_data="admin_video_guide"))
    await callback.message.edit_text(get_text("confirm_delete_guide", lang), reply_markup=builder.as_markup())

@router.callback_query(F.data == "admin_delete_guide_confirm")
async def admin_delete_guide_confirm_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id): return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'
    await db.delete_setting('video_guide_file_id')
    await callback.answer(get_text("guide_deleted_success", lang), show_alert=True)
    await callback.message.edit_text(get_text("admin_video_guide_menu", lang), reply_markup=await admin_video_guide_keyboard(lang)) # noqa

@router.callback_query(F.data.startswith("perm_"))
async def admin_permission_grant_revoke(callback: CallbackQuery):
    _, perm_type, value, user_id = callback.data.split("_")
    user_id = int(user_id)
    value = int(value)
    lang = 'uz'

    if perm_type == "admin":
        await db.update_user_field(user_id, "is_admin", value)
        await callback.answer(get_text("admin_granted", lang) if value else get_text("admin_revoked", lang), show_alert=True)
    elif perm_type == "special":
        await db.update_user_field(user_id, "is_special_user", value)
        await callback.answer(get_text("special_granted", lang) if value else get_text("special_revoked", lang), show_alert=True)

    # Menyuni yangilash (Foydalanuvchi profiliga qaytish)
    await show_user_profile_admin(callback.message, user_id, lang)

@router.message(StateFilter(AdminStates.user_selection))
async def admin_user_selection_handler(message: Message, state: FSMContext):
    lang = 'uz'
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await clear_state_preserve_session(state)
        await message.answer("Bekor qilindi.", reply_markup=admin_keyboard(lang))
        return

    data = await state.get_data()
    mapping = data.get("user_mapping", {})

    try:
        selection = int(message.text)
        user_id = mapping.get(selection)
        if user_id:
            await show_user_profile_admin(message, user_id, lang)
            await clear_state_preserve_session(state)
        else:
            await message.answer("Noto'g'ri raqam! Qayta urinib ko'ring.")
    except ValueError:
        await message.answer("Iltimos, raqam kiriting.")

async def show_user_profile_admin(message_obj, user_id, lang):
    user = await db.get_user(user_id)
    if not user:
        await message_obj.answer("Foydalanuvchi topilmadi.")
        return

    # Foydalanuvchi ma'lumotlarini ko'rsatish
    full_name = escape(user[4]) if user[4] else get_text('lbl_none', lang)
    region = escape(user[5]) if user[5] else get_text('lbl_none', lang)
    district = escape(user[6]) if user[6] else get_text('lbl_none', lang)
    neighborhood = escape(user[7]) if user[7] else get_text('lbl_none', lang)
    phone = escape(user[8]) if user[8] else get_text('lbl_none', lang)
    location = user[9] if len(user) > 9 else None
    
    loc_link = f"<a href='https://maps.google.com/?q={location}'>Xaritada ko'rish</a>" if location else get_text('lbl_none', lang)
    blocked_status = "Ha" if (len(user) > 10 and user[10]) else "Yo'q"
    username_link = f"@{user[1]}" if user[1] else get_text('lbl_none', lang)
    
    joined_at = "Noma'lum"
    if len(user) > 11 and user[11]:
        try:
            dt = datetime.fromisoformat(user[11]).astimezone(UZ_TIMEZONE)
            joined_at = dt.strftime("%d.%m.%Y %H:%M")
        except: pass

    text = (
        f"👤 <b>Foydalanuvchi ma'lumotlari:</b>\n\n"
        f"ID: {user[0]}\n"
        f"👤 Username: {username_link}\n"
        f"👤 To'liq ism: {full_name}\n"
        f"📞 Telefon: {phone}\n" # noqa
        f"🌍 Viloyat: {region}\n" # noqa
        f"🏘 Tuman: {district}\n" # noqa
        f"🏠 Mahalla: {neighborhood}\n" # noqa
        f"📍 Manzil: {loc_link}\n" # noqa
        f"🚫 Bloklangan: {blocked_status}\n"
        f"Qo'shilgan: {joined_at}\n"
    )
    
    is_admin = await db.is_user_admin(user_id)
    is_special = await db.is_special_user(user_id)
    is_banned = (len(user) > 10 and user[10] == 1)
    await message_obj.answer(text, parse_mode="HTML", disable_web_page_preview=True, reply_markup=admin_user_actions_keyboard(user_id, is_banned, is_admin, is_special, lang)) # noqa

@router.callback_query(F.data.startswith("admin_block_") | F.data.startswith("admin_unblock_"))
async def admin_block_unblock_handler(callback: CallbackQuery, state: FSMContext):
    """Foydalanuvchini bloklash va blokdan chiqarish uchun birlashtirilgan handler."""
    parts = callback.data.split('_')
    action = parts[1]
    user_id = int(parts[2])
    is_blocking = (action == "block")
    
    if is_blocking:
        await db.ban_user(user_id)
        answer_text = get_text("admin_user_blocked", 'uz')
        try:
            user_lang = await get_user_lang(user_id)
            kb = blocked_user_keyboard(user_lang)
            await callback.bot.send_message(user_id, get_text("user_blocked_by_admin", user_lang, name=callback.from_user.first_name), reply_markup=kb)
        except: pass
    else: # unblocking
        await db.update_user_field(user_id, "is_banned", 0)
        answer_text = get_text("admin_user_unblocked", 'uz')
        try:
            user_lang = await get_user_lang(user_id)
            await callback.bot.send_message(user_id, get_text("user_unblocked_alert", user_lang, name=callback.from_user.first_name))
        except: pass

    await callback.answer(answer_text) # noqa
    await callback.message.edit_text(answer_text, reply_markup=back_to_admin_keyboard())
    await clear_state_preserve_session(state)

@router.callback_query(F.data.startswith("admin_notify_"))
async def admin_notify_callback(callback: CallbackQuery, state: FSMContext):
    user_id = int(callback.data.split("_")[2])
    lang = 'uz'
    await state.update_data(notify_user_id=user_id)
    await state.set_state(AdminStates.send_notification)
    await callback.message.answer(get_text("admin_enter_notify", lang), reply_markup=cancel_keyboard(lang))
    await callback.answer()

@router.message(StateFilter(AdminStates.send_notification))
async def admin_send_notification_handler(message: Message, state: FSMContext):
    data = await state.get_data()
    user_id = data.get("notify_user_id")
    lang = 'uz'
    
    if user_id:
        try:
            await message.bot.send_message(user_id, f"📩 <b>Admin xabari:</b>\n\n{escape(message.text)}", parse_mode="HTML")
            await message.answer(get_text("admin_notify_sent", lang), reply_markup=back_to_admin_keyboard())
        except Exception as e: # noqa
            await message.answer(f"Xatolik: {e}", reply_markup=back_to_admin_keyboard())
    
    await clear_state_preserve_session(state)

@router.callback_query(F.data == "admin_cancel_action")
async def admin_cancel_action(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    await callback.message.edit_text("Harakat bekor qilindi.", reply_markup=back_to_admin_keyboard())


@router.callback_query(F.data == "admin_orders")
async def orders_handler(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    await show_admin_orders(callback, state, page=0)
async def show_admin_orders(callback: CallbackQuery, state: FSMContext, page: int):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return

    # Admin panel faqat o'zbek tilida # noqa
    lang = 'uz' 
    orders = await db.get_orders()
    if not orders:
        await safe_edit_message(callback, "Buyurtmalar yo'q.", reply_markup=admin_keyboard(lang))
        return

    ITEMS_PER_PAGE = 5
    total_pages = (len(orders) + ITEMS_PER_PAGE - 1) // ITEMS_PER_PAGE
    start_idx = page * ITEMS_PER_PAGE
    end_idx = start_idx + ITEMS_PER_PAGE
    current_orders = orders[start_idx:end_idx]

    text = get_text("admin_orders_list", lang) + "\n\n"
    mapping = {}

    for idx, order in enumerate(current_orders, 1):
        real_idx = start_idx + idx
        # order: (order_id, user_id, order_text, status, created_at, order_type, platform, media_file_id, media_type)
        order_id, user_id, order_text, status = order[0], order[1], order[2], order[3]
        created_at = order[4] if len(order) > 4 else "Noma'lum"
        
        # Yangi ustunlarni tekshirish (agar baza yangilangan bo'lsa)
        order_type = order[5] if len(order) > 5 else "Noma'lum"
        platform = order[6] if len(order) > 6 else "Noma'lum"
        
        user = await db.get_user(user_id)
        username = user[1] if user else "noma'lum"
        
        mapping[real_idx] = order_id
        text += f"<b>{real_idx}.</b> ID: {order_id} | User: @{username}\nTur: {order_type} | Plat: {platform}\nStatus: {status}\n\n"

    await state.update_data(order_mapping=mapping)
    await state.set_state(AdminStates.viewing_orders)

    builder = InlineKeyboardBuilder()
    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton(text="⬅️ Oldingi", callback_data=f"admin_orders_page_{page-1}"))
    
    nav_row.append(InlineKeyboardButton(text=f"📄 {page+1}/{total_pages}", callback_data="noop"))

    if (page + 1) < total_pages:
        nav_row.append(InlineKeyboardButton(text="Keyingi ➡️", callback_data=f"admin_orders_page_{page+1}"))
    
    builder.row(*nav_row)
    builder.row(InlineKeyboardButton(text=get_text("admin_back", lang), callback_data="admin_panel"))

    await safe_edit_message(callback, text, reply_markup=builder.as_markup())

@router.callback_query(F.data.startswith("admin_orders_page_"))
async def admin_orders_pagination(callback: CallbackQuery, state: FSMContext):
    page = int(callback.data.split("_")[3])
    await show_admin_orders(callback, state, page)

@router.message(StateFilter(AdminStates.viewing_orders))
async def admin_order_selection_handler(message: Message, state: FSMContext):
    lang = 'uz'
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await clear_state_preserve_session(state)
        await message.answer("Bekor qilindi.", reply_markup=back_to_admin_keyboard())
        return

    data = await state.get_data()
    mapping = data.get("order_mapping", {})

    try:
        selection = int(message.text)
        order_id = mapping.get(selection)
        if order_id:
            # Buyurtma tafsilotlarini ko'rsatish
            order = await db.get_order(order_id)
            if not order:
                await message.answer("Buyurtma topilmadi.")
                return
            
            user_id = order[1]
            user = await db.get_user(user_id)
            profile_text = await get_user_profile_text(user, lang)
            
            order_text = order[2]
            order_type = order[5] if len(order) > 5 else "-"
            platform = order[6] if len(order) > 6 else "-"
            media_id = order[7] if len(order) > 7 else None
            media_type = order[8] if len(order) > 8 else None
            
            detail_text = (
                f"📦 <b>Buyurtma #{order_id}</b>\n\n"
                f"{profile_text}\n\n"
                f"📌 Tur: {order_type}\n"
                f"📱 Platforma: {platform}\n"
                f"📝 Matn: {order_text}"
            )
            
            builder = InlineKeyboardBuilder()
            builder.add(InlineKeyboardButton(text=get_text("btn_completed", lang), callback_data=f"admin_order_complete_{order_id}"))
            builder.add(InlineKeyboardButton(text=get_text("btn_later", lang), callback_data=f"admin_order_later_{order_id}"))
            builder.add(InlineKeyboardButton(text="🗑️ O'chirish", callback_data=f"admin_order_delete_{order_id}"))
            builder.add(InlineKeyboardButton(text="⬅️ Orqaga", callback_data="admin_orders"))
            builder.adjust(1)
            
            if media_id and media_type:
                if media_type == "photo": await message.answer_photo(media_id, caption=detail_text, parse_mode="HTML", reply_markup=builder.as_markup())
                elif media_type == "video": await message.answer_video(media_id, caption=detail_text, parse_mode="HTML", reply_markup=builder.as_markup())
                elif media_type == "document": await message.answer_document(media_id, caption=detail_text, parse_mode="HTML", reply_markup=builder.as_markup())
            else:
                await message.answer(detail_text, parse_mode="HTML", reply_markup=builder.as_markup(), disable_web_page_preview=True)
        else:
            await message.answer("Noto'g'ri raqam! Qayta urinib ko'ring.")
    except ValueError:
        await message.answer("Iltimos, raqam kiriting.")

@router.callback_query(F.data.startswith("admin_order_delete_"))
async def admin_order_delete_callback(callback: CallbackQuery, state: FSMContext):
    order_id = int(callback.data.split("_")[3])
    lang = 'uz'
    # Sharh: Buyurtmani o'chirish uchun `database.py` dagi maxsus metod chaqirilmoqda.
    # Bu kodning bir xilligini va markazlashtirilgan ma'lumotlar bazasi boshqaruvini ta'minlaydi.
    await db.delete_order(order_id) # noqa
    await callback.answer(get_text("order_deleted", lang), show_alert=True)
    try:
        await callback.message.delete()
    except Exception:
        pass
    await callback.bot.send_message(callback.from_user.id, get_text("admin_welcome", lang), reply_markup=admin_keyboard(lang))

@router.callback_query(F.data.startswith("admin_order_complete_"))
async def admin_order_complete_callback(callback: CallbackQuery, state: FSMContext):
    order_id = int(callback.data.split("_")[3])
    lang = 'uz'
    
    await db.update_order_status(order_id, "Bajarildi ✅")
    
    # Foydalanuvchiga xabar
    order = await db.get_order(order_id)
    if order:
        user_id = order[1]
        try:
            await callback.bot.send_message(user_id, get_text("order_status_completed_msg", await get_user_lang(user_id))) # noqa
        except: pass

    # Xabarni o'chirish
    try:
        await callback.message.delete()
    except Exception:
        pass
    
    # 3 soniya xabar ko'rsatish
    msg = await callback.bot.send_message(callback.from_user.id, "Buyurtma bajarildi! ✅")
    await asyncio.sleep(3)
    await msg.delete()
    
    await callback.bot.send_message(callback.from_user.id, get_text("admin_welcome", lang), reply_markup=admin_keyboard(lang))
    await callback.answer()

@router.callback_query(F.data.startswith("admin_order_later_"))
async def admin_order_later_callback(callback: CallbackQuery, state: FSMContext):
    order_id = int(callback.data.split("_")[3])
    lang = 'uz'
    
    await db.update_order_status(order_id, "Keyinroq ⏳")
    
    # Foydalanuvchiga xabar
    order = await db.get_order(order_id)
    if order:
        user_id = order[1]
        try:
            await callback.bot.send_message(user_id, get_text("order_status_later_msg", await get_user_lang(user_id))) # noqa
        except: pass

    await callback.answer("Buyurtma keyinga qoldirildi.", show_alert=True)
    await show_admin_orders(callback, state, page=0)

@router.callback_query(F.data == "admin_search_user")
async def admin_search_user_handler(callback: CallbackQuery, state: FSMContext):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida # noqa
    lang = 'uz' 

    await state.set_state(AdminStates.search_user_id)
    await callback.message.edit_text("Qidirmoqchi bo'lgan foydalanuvchining ID'sini kiriting:", reply_markup=back_to_admin_keyboard())


@router.message(StateFilter(AdminStates.search_user_id))
async def admin_search_user_by_id(message: Message, state: FSMContext):
    lang = 'uz'
    if message.text in ("🏠 Bosh menyuga", "❌ Bekor qilish"):
        await clear_state_preserve_session(state)
        await message.answer("Bekor qilindi.", reply_markup=admin_keyboard(lang))
        return

    try:
        user_id_to_find = int(message.text)
        user = await db.get_user(user_id_to_find)

        if user:
            await show_user_profile_admin(message, user_id_to_find, lang)
        else:
            await message.answer(get_text("admin_user_id_not_found", lang))
    except ValueError:
        await message.answer("Iltimos, to'g'ri foydalanuvchi ID'sini kiriting (faqat raqamlar).")
    await clear_state_preserve_session(state)

@router.callback_query(F.data == "admin_export_excel")
async def admin_export_excel_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):
        await callback.answer("Siz admin emassiz! ❌", show_alert=True)
        return
    # Admin panel faqat o'zbek tilida
    lang = 'uz'

    await callback.answer("Fayl tayyorlanmoqda, iltimos kuting...", show_alert=False)

    users = await db.get_all_users()
    if not users:
        await callback.message.answer("Yuklab olish uchun foydalanuvchilar yo'q.", reply_markup=admin_keyboard(lang))
        return
    
    file_path = f"users_export_{datetime.now().strftime('%Y-%m-%d')}.xlsx"
    
    # Sharh: Excel faylini yaratish sinxron va ko'p foydalanuvchida botni bloklashi mumkin.
    # Shuning uchun bu jarayonni `run_in_executor` yordamida fon rejimiga o'tkazamiz.
    def generate_excel_sync():
        try:
            workbook = openpyxl.Workbook()
            sheet = workbook.active
            sheet.title = "Foydalanuvchilar"

            headers = [
                "ID", "Username", "Telegram Ism", "Kiritilgan F.I.O",
                "Telefon", "Viloyat", "Tuman", "Mahalla", "Qo'shilgan vaqti"
            ]
            sheet.append(headers)

            for user in users:
                user_id, username, first_name, _, full_name, region, district, neighborhood, phone, _, _, joined_at_iso, *_ = user + (None,) * (12 - len(user))
                
                def format_date(iso_string):
                    if not iso_string: return "Noma'lum"
                    try:
                        dt = datetime.fromisoformat(iso_string).astimezone(UZ_TIMEZONE)
                        return dt.strftime("%d.%m.%Y %H:%M:%S")
                    except (ValueError, TypeError): return "Noma'lum"

                joined_at = format_date(joined_at_iso)
                sheet.append([
                    user_id, username, first_name, full_name,
                    phone, region, district, neighborhood, joined_at
                ])

            for column in sheet.columns:
                max_length = 0
                column_letter = column[0].column_letter
                for cell in column:
                    try:
                        if len(str(cell.value)) > max_length:
                            max_length = len(str(cell.value))
                    except: pass
                adjusted_width = (max_length + 2)
                sheet.column_dimensions[column_letter].width = adjusted_width

            workbook.save(file_path)
            return True
        except Exception as e:
            logger.error(f"Excel faylini yaratishda ichki xato: {e}")
            return False

    loop = asyncio.get_event_loop()
    success = await loop.run_in_executor(None, generate_excel_sync)

    if success and os.path.exists(file_path):
        document = FSInputFile(file_path, filename=f"foydalanuvchilar_{datetime.now().strftime('%Y-%m-%d')}.xlsx")
        await callback.message.answer_document(document, caption="Foydalanuvchilar ro'yxati Excel formatida.")
    else:
        await callback.message.answer(get_text("excel_error", lang))
    
    if os.path.exists(file_path):
        await safe_remove(file_path)

# ============================================================
# YORDAMCHI: Aqlli Video Yuborish (Smart Send)
# ============================================================
async def smart_send_video(
    bot: Bot,
    chat_id: int,
    file_path: str,
    caption: str,
    width: int = None,
    height: int = None,
    duration: int = None,
    reply_markup=None,
):
    """Videoni bot nomidan yuboradi. 50MB+ fayl: userbot -> storage channel -> Bot API copy."""
    global user_bot
    if not os.path.isfile(file_path) or os.path.getsize(file_path) <= 0:
        logger.error("Smart send video: fayl topilmadi yoki bo'sh: %s", file_path)
        return None
    file_size = os.path.getsize(file_path)

    if file_size <= 50 * 1024 * 1024:
        return await bot.send_video(
            chat_id=chat_id, video=FSInputFile(file_path), caption=caption,
            parse_mode="HTML", width=width, height=height, duration=duration,
            reply_markup=reply_markup, request_timeout=600,
        )

    if not user_bot or not UPLOAD_CHANNEL_ID:
        logger.error("Katta video uchun userbot yoki UPLOAD_CHANNEL_ID mavjud emas.")
        return None

    try:
        # Userbot faqat storage kanaliga yuklaydi; foydalanuvchiga hech qachon
        # userbot akkauntidan to'g'ridan-to'g'ri yubormaymiz.
        channel_msg = await user_bot.send_video(
            chat_id=int(UPLOAD_CHANNEL_ID),
            video=file_path,
            width=width, height=height, duration=duration,
            supports_streaming=True,
            caption="Dono Bot storage",
        )
        channel_message_id = int(channel_msg.id)

        # Bot API copyMessage server-side nusxalaydi va xabarni BOT nomidan yuboradi.
        copied = await bot.copy_message(
            chat_id=chat_id,
            from_chat_id=int(UPLOAD_CHANNEL_ID),
            message_id=channel_message_id,
            caption=caption,
            parse_mode="HTML",
            reply_markup=reply_markup,
        )
        logger.info("Katta video bot nomidan yuborildi: channel_message_id=%s", channel_message_id)
        return {"channel_message_id": channel_message_id, "copied_message_id": getattr(copied, "message_id", None)}
    except (SessionRevoked, AuthKeyUnregistered, UserDeactivated) as exc:
        logger.error("Userbot sessiyasi yaroqsiz: %s", exc)
        try:
            await user_bot.stop()
        except Exception:
            pass
        user_bot = None
    except Exception as exc:
        logger.error("Katta videoni storage channel -> bot orqali yuborishda xato: %s", exc, exc_info=True)
    return None

async def smart_send_audio(
    bot: Bot,
    chat_id: int,
    file_path: str,
    caption: str,
    title: str = None,
    performer: str = None,
    duration: int = None,
    reply_markup=None,
):
    """Audioni hajmiga qarab xavfsiz yuboradi."""
    global user_bot
    if not os.path.isfile(file_path):
        return None
    file_size = os.path.getsize(file_path)
    if file_size <= 0:
        return None

    if file_size <= 50 * 1024 * 1024:
        return await bot.send_audio(
            chat_id=chat_id, audio=FSInputFile(file_path), caption=caption,
            parse_mode="HTML", title=title, performer=performer, duration=duration,
            reply_markup=reply_markup, request_timeout=600
        )

    if user_bot:
        try:
            return await user_bot.send_audio(
                chat_id=chat_id, audio=file_path, caption=re.sub(r"<[^>]+>", "", caption),
                title=title, performer=performer, duration=duration
            )
        except (SessionRevoked, AuthKeyUnregistered, UserDeactivated) as exc:
            logger.error("Userbot sessiyasi yaroqsiz: %s", exc)
            try:
                await user_bot.stop()
            except Exception:
                pass
            user_bot = None
        except Exception as exc:
            logger.error("Katta audioni userbot orqali yuborishda xato: %s", exc, exc_info=True)

    lang = await get_user_lang(chat_id)
    await bot.send_message(chat_id, get_text("file_too_large", lang))
    return None

# ============================================================
# Admin Panel - Userbot orqali video yuklash (foydalanuvchi so'rovi)
# ============================================================
@router.message(Command("upload_video_channel"), lambda m: m.from_user.id in ADMIN_IDS)
async def upload_video_to_channel_handler(message: Message, bot: Bot):
    """
    global user_bot
    Admin uchun userbot yordamida kanalgacha katta videolarni (2GB gacha) yuklash.
    Ishlatish: Videoga reply qilib /upload_video_channel buyrug'ini yozing.
    """
    # 1. Userbot sozlanmagan bo'lsa, xabar berish
    if not user_bot:
        await message.reply("Userbot sozlanmagan! .env fayliga API_ID va API_HASH ni kiriting.")
        return

    # 2. Buyruq video faylga javob (reply) qilib yuborilganini tekshirish
    if not message.reply_to_message or not message.reply_to_message.video:
        await message.reply("Iltimos, video faylga javob (reply) qilib /upload_video_channel buyrug'ini yuboring.")
        return

    # 3. Yuklash uchun kanal IDsi .env faylida borligini tekshirish
    if not UPLOAD_CHANNEL_ID:
        await message.reply("UPLOAD_CHANNEL_ID o'zgaruvchisi .env faylida ko'rsatilmagan!")
        return

    video = message.reply_to_message.video
    status_msg = await message.reply("⏳ Video botga yuklab olinmoqda...")

    os.makedirs("uploads", exist_ok=True)
    file_path = f"uploads/{video.file_id}.mp4"

    try:
        # 4. Videoni bot serveriga yuklab olish
        await bot.download(video, destination=file_path)
        await status_msg.edit_text("✅ Video yuklab olindi. Endi kanalga yuklanmoqda...")

        # 5. Progressni ko'rsatish uchun funksiyani tayyorlash
        last_update_time = [time.time()]
        progress_callback = partial(upload_progress_hook, bot=bot, message=status_msg, last_update_time=last_update_time)
        
        # 6. Userbot orqali kanalga yuborish
        await user_bot.send_video(
            chat_id=int(UPLOAD_CHANNEL_ID),
            video=file_path,
            caption=message.reply_to_message.caption or "",
            progress=progress_callback
        )
        
        await status_msg.edit_text("✅ Video kanalga muvaffaqiyatli yuklandi!")

    except (SessionRevoked, AuthKeyUnregistered, UserDeactivated) as e:
        await status_msg.edit_text("❌ Userbot sessiyasi yaroqsiz bo'lib qoldi. Sessiya fayli o'chirildi. Botni qayta ishga tushiring.")
        if os.path.exists("my_account.session"):
            os.remove("my_account.session")
        user_bot = None

    except Exception as e:
        logger.error(f"Kanalga video yuklashda xato: {e}")
        await status_msg.edit_text("❌ Video kanalga yuklashda ichki xatolik yuz berdi. Log tekshiriladi.")
    finally:
        # 7. Vaqtinchalik faylni o'chirish
        if os.path.exists(file_path):
            await safe_remove(file_path)

@router.callback_query(StateFilter(UserStates.settings), F.data.startswith("set_lang_")) # noqa
async def set_language_callback(callback: CallbackQuery, state: FSMContext):
    selected_lang = callback.data.split("_")[2] # noqa
    user_id = callback.from_user.id
    current_lang = await get_user_lang(user_id)
    
    # Tanlangan tilni ko'rsatish va saqlash tugmasini chiqarish
    lang_name = get_text(f"lang_{selected_lang}", selected_lang)
    msg_text = get_text("selected", selected_lang, l_name=lang_name)
    await callback.message.edit_text(msg_text, reply_markup=settings_language_keyboard(current_lang, selected_lang))
 # noqa
@router.callback_query(StateFilter(UserStates.settings), F.data.startswith("save_lang_"))
async def save_language_callback(callback: CallbackQuery, state: FSMContext):
    new_lang = callback.data.split("_")[2]
    user_id = callback.from_user.id
    await db.set_user_language(user_id, new_lang)
    await clear_state_preserve_session(state)
    
    # Foydalanuvchi ismini olish
    user = await db.get_user(user_id)
    has_profile = await db.has_profile(user_id)
    display_name = user[4] if (has_profile and user and user[4]) else callback.from_user.first_name
    
    is_admin = await is_user_admin(user_id)
    await callback.message.edit_text(get_text("saved", new_lang), reply_markup=main_menu_keyboard(is_admin=is_admin, lang=new_lang, user_name=display_name))

# ============================================================
# Tarjima Bo'limi (Adminlar uchun)
# ============================================================

def language_selection_keyboard(lang: str, prefix: str):
    """Til tanlash uchun klaviatura yaratuvchi yordamchi funksiya."""
    builder = InlineKeyboardBuilder()
    builder.add(InlineKeyboardButton(text=get_text("lang_en", lang), callback_data=f"{prefix}_en"))
    builder.add(InlineKeyboardButton(text=get_text("lang_ru", lang), callback_data=f"{prefix}_ru"))
    builder.add(InlineKeyboardButton(text=get_text("lang_uz", lang), callback_data=f"{prefix}_uz"))
    builder.row(InlineKeyboardButton(text=get_text("back_main", lang), callback_data="menu_main"))
    builder.adjust(3, 1)
    builder.adjust(1)
    return builder.as_markup()

@router.callback_query(F.data == "menu_translate")
async def translate_menu_handler(callback: CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    lang = await get_user_lang(user_id)
    await state.set_state(TranslationStates.select_source_lang)
    await callback.message.edit_text(
        get_text("select_source_language", lang),
        reply_markup=language_selection_keyboard(lang, "translate_from")
    )
    await callback.answer()

@router.callback_query(StateFilter(TranslationStates.select_source_lang), F.data.startswith("translate_from_"))
async def select_source_lang_handler(callback: CallbackQuery, state: FSMContext):
    source_lang = callback.data.rsplit("_", 1)[-1]
    if source_lang not in {"uz", "ru", "en"}:
        await callback.answer("⚠️ Til noto'g'ri.", show_alert=True)
        return
    await state.update_data(source_lang=source_lang)
    await state.set_state(TranslationStates.enter_text)
    lang = await get_user_lang(callback.from_user.id)
    await callback.message.edit_text(get_text("enter_text_for_translation", lang), reply_markup=cancel_keyboard(lang))
    await callback.answer()

@router.message(StateFilter(TranslationStates.enter_text), F.text)
async def enter_text_for_translation_handler(message: Message, state: FSMContext):
    text_to_translate = (message.text or "").strip()
    if not text_to_translate:
        await message.answer("⚠️ Iltimos, matn yuboring.")
        return
    if len(text_to_translate) > 5000:
        await message.answer("⚠️ Matn 5000 belgidan oshmasin.")
        return
    await state.update_data(text_to_translate=text_to_translate)
    await state.set_state(TranslationStates.select_target_lang)
    lang = await get_user_lang(message.from_user.id)
    await message.answer(
        get_text("select_target_language", lang),
        reply_markup=language_selection_keyboard(lang, "translate_to")
    )

@router.callback_query(StateFilter(TranslationStates.select_target_lang), F.data.startswith("translate_to_"))
async def select_target_lang_handler(callback: CallbackQuery, state: FSMContext):
    target_lang = callback.data.rsplit("_", 1)[-1]
    if target_lang not in {"uz", "ru", "en"}:
        await callback.answer("⚠️ Til noto'g'ri.", show_alert=True)
        return

    data = await state.get_data()
    source_lang = data.get("source_lang")
    text_to_translate = (data.get("text_to_translate") or "").strip()
    lang = await get_user_lang(callback.from_user.id)

    if source_lang not in {"uz", "ru", "en"} or not text_to_translate:
        await callback.answer("⚠️ Tarjima sessiyasi eskirgan. Qaytadan urinib ko'ring.", show_alert=True)
        await state.clear()
        return

    cache_key = hashlib.sha256(
        f"{source_lang}:{target_lang}:{text_to_translate}".encode("utf-8")
    ).hexdigest()
    cached = _TRANSLATION_CACHE.get(cache_key)
    if cached:
        await callback.message.edit_text(
            f"<b>Tarjima:</b>\n\n{escape(cached)}",
            parse_mode="HTML",
            reply_markup=back_to_main_keyboard(lang),
        )
        await callback.answer()
        await state.clear()
        return

    try:
        await callback.answer("🔄 Tarjima qilinmoqda...")
        await callback.message.edit_text("🔄 Tarjima qilinmoqda...", parse_mode="HTML")
        translated_text = await asyncio.to_thread(
            _translate_sync, source_lang, target_lang, text_to_translate
        )
        if not translated_text or not str(translated_text).strip():
            raise RuntimeError("Bo'sh tarjima qaytdi")
        translated_text = str(translated_text).strip()
        _TRANSLATION_CACHE[cache_key] = translated_text
        if len(_TRANSLATION_CACHE) > 500:
            for old_key in list(_TRANSLATION_CACHE)[:100]:
                _TRANSLATION_CACHE.pop(old_key, None)

        await callback.message.edit_text(
            f"<b>Tarjima:</b>\n\n{escape(translated_text)}",
            parse_mode="HTML",
            reply_markup=back_to_main_keyboard(lang),
        )
    except Exception as exc:
        logger.error("Tarjima xatosi: %s", exc, exc_info=True)
        await callback.message.edit_text(
            "⚠️ Tarjima vaqtincha ishlamadi. Internet yoki tarjima serverini tekshirib, qayta urinib ko'ring.",
            reply_markup=back_to_main_keyboard(lang),
        )
    finally:
        await state.clear()


# ============================================================
# Tugma va handler xavfsizlik himoyasi
# ============================================================
@router.callback_query()
async def stale_or_unhandled_callback(callback: CallbackQuery, state: FSMContext):
    """Eskirgan yoki hech qaysi handlerga mos kelmagan tugmani jim qoldirmaydi."""
    try:
        await callback.answer("⚠️ Bu tugma eskirgan. /start ni bosing.", show_alert=True)
    except Exception:
        pass


@router.errors()
async def router_error_handler(event):
    """Bitta handler xatosi sabab polling to'xtab qolmasligi uchun."""
    exc = getattr(event, "exception", None)
    logger.error("Handler xatosi: %s", exc, exc_info=True)
    update = getattr(event, "update", None)
    callback = getattr(update, "callback_query", None)
    if callback:
        try:
            await callback.answer("⚠️ Xatolik yuz berdi. /start ni bosing.", show_alert=True)
        except Exception:
            pass


# ============================================================
# Main — Bot ishga tushish
# ============================================================
def is_userbot_lock_error(exc: Exception) -> bool:
    """Pyrogram session sqlite lock bilan bog'liq xatolarni aniqlaydi."""
    err_text = str(exc).lower()
    lock_markers = (
        "database is locked",
        "database table is locked",
        "database schema is locked",
        "session is locked",
        "sqlite_busy",
        "sqlite_locked",
        "resource temporarily unavailable",
    )
    if isinstance(exc, sqlite3.OperationalError):
        return any(marker in err_text for marker in lock_markers)
    return any(marker in err_text for marker in lock_markers)


async def start_userbot_with_retry() -> Any:
    """Userbotni xavfsiz ishga tushiradi; lock bo'lsa cheklangan retry qiladi."""
    for attempt in range(1, USERBOT_START_MAX_RETRIES + 1):
        candidate = Client(
            "my_account",
            api_id=int(API_ID),
            api_hash=API_HASH,
            app_version="1.0.0",
            device_model="DonoBotServer",
            ipv6=False,
            no_updates=True
        )
        try:
            await candidate.start()
            if attempt > 1:
                logger.info(f"✅ Userbot {attempt}-urinishda muvaffaqiyatli ishga tushdi.")
            return candidate
        except Exception as e:
            try:
                await candidate.stop()
            except Exception:
                pass

            if is_userbot_lock_error(e) and attempt < USERBOT_START_MAX_RETRIES:
                wait_seconds = USERBOT_START_BACKOFF_SECONDS * attempt
                logger.warning(
                    f"⚠️ Userbot session lock xatosi (urinish {attempt}/{USERBOT_START_MAX_RETRIES}): {e}. "
                    f"{wait_seconds}s dan so'ng qayta uriniladi."
                )
                await asyncio.sleep(wait_seconds)
                continue
            raise
    return None


async def main():
    # Userbot obyektini global o'zgaruvchiga o'rnatish (bot ishga tushganda)
    global user_bot, USERBOT_SESSION_NEEDS_RESET, UPLOAD_CHANNEL_ID
    
    if PYROGRAM_AVAILABLE and API_ID and API_HASH:
        if os.path.exists(userbot_session_journal_path):
            # Ko'pincha server qayta ishga tushganda journal qolib ketadi va sqlite lock beradi.
            try:
                os.remove(userbot_session_journal_path)
                logger.warning("♻️ Stale userbot session journal o'chirildi.")
            except Exception as e:
                logger.warning(f"Session journal o'chirilmadi: {e}")
        try:
            user_bot = await start_userbot_with_retry()
            logger.info("✅ Userbot muvaffaqiyatli ulandi!")
        except SessionRevoked:
            logger.error("❌ Userbot SESSION_REVOKED xatosi. Sessiya o'chiriladi...")
            if os.path.exists(userbot_session_path):
                try:
                    os.remove(userbot_session_path)
                    logger.info("♻️ SESSION_REVOKED xatosi uchun sessiya fayli o'chirildi.")
                except: pass
            user_bot = None
        except (AuthKeyUnregistered, UserDeactivated) as e:
            logger.error(f"❌ Userbot autentifikatsiya xatosi: {e}. Sessiya o'chiriladi...")
            if os.path.exists(userbot_session_path):
                try:
                    os.remove(userbot_session_path)
                except: pass
            user_bot = None
        except Exception as e:
            if is_userbot_lock_error(e):
                logger.error(
                    "❌ Userbot session lock sababli ishga tushmadi. "
                    "Boshqa jarayon shu sessiyani ishlatayotgan bo'lishi mumkin. "
                    "Barcha bot/userbot jarayonlarini to'xtating, "
                    f"`{userbot_session_journal_path}` fayli qolgan bo'lsa o'chiring va qayta ishga tushiring. "
                    "Agar muammo davom etsa, sessiyani qayta autentifikatsiya qiling."
                )
            else:
                logger.error(f"❌ Userbot (Pyrogram) ishga tushmadi: {e}")
            user_bot = None

    if not BOT_TOKEN:
        logger.error("BOT_TOKEN topilmadi! .env faylini tekshiring.")
        return

    bot = Bot(token=BOT_TOKEN)

    # Katta fayl oqimi uchun Bot storage kanaliga kirish huquqini tekshiramiz.
    # Bot admin/member bo'lmasa copyMessage ishlamaydi; buni yuklash paytida emas,
    # start vaqtida aniqlash qotib qolish va noto'g'ri xabarlarni kamaytiradi.
    if UPLOAD_CHANNEL_ID:
        try:
            me = await bot.get_me()
            member = await bot.get_chat_member(int(UPLOAD_CHANNEL_ID), me.id)
            if getattr(member, "status", None) not in {"administrator", "creator"}:
                logger.error("UPLOAD_CHANNEL_ID kanalida bot admin emas: katta fayl oqimi o'chiriladi.")
                UPLOAD_CHANNEL_ID = None
            else:
                logger.info("✅ Storage kanalga Bot API kirishi tasdiqlandi.")
        except Exception as exc:
            logger.error("Storage kanal tekshiruvi muvaffaqiyatsiz: %s", exc)
            UPLOAD_CHANNEL_ID = None

    dp = Dispatcher(storage=storage)
    dp.include_router(router)

    # Bazani ishga tushirish (async)
    await db.setup()

    # Eski foydalanuvchilarni davriy tozalash: Telegram online holati Bot API orqali olinmaydi,
    # shuning uchun mezon bot bilan oxirgi aloqa (`last_active`) hisoblanadi.
    async def inactive_user_cleanup_loop():
        while True:
            try:
                deleted = await db.delete_inactive_users(days=7, batch_size=500)
                if deleted:
                    logger.info("🧹 7 kundan beri faol bo'lmagan %s ta foydalanuvchi tozalandi.", deleted)
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                logger.error("Inactive user cleanup xatosi: %s", exc, exc_info=True)
            await asyncio.sleep(6 * 60 * 60)

    cleanup_task = asyncio.create_task(inactive_user_cleanup_loop())

    # Yuklash papkalarini yaratish
    os.makedirs("downloads", exist_ok=True)
    os.makedirs("uploads", exist_ok=True)

    # Middleware qo'shish (to'g'ri usul)
    subscription_middleware = SubscriptionMiddleware(bot)
    dp.message.middleware(subscription_middleware)
    dp.callback_query.middleware(subscription_middleware)

    if user_bot:
        logger.info("✅ Userbot tayyor (katta fayllar uchun)")
    else:
        logger.warning("⚠️ Userbot yo'q — 50MB+ fayllar cheklangan bo'lishi mumkin")

    try:
        import tgcrypto  # noqa: F401
    except ImportError:
        logger.warning(
            "TgCrypto o'rnatilmagan — Pyrogram sekinroq ishlaydi. "
            "Tezlik uchun: pip install tgcrypto"
        )

    logger.info("✅ Bot ishga tushdi!")

    try:
        await bot.delete_webhook(drop_pending_updates=False)
        await dp.start_polling(bot)
    except Exception as e:
        logger.error("Bot ishga tushishda xato: %s", e)
    finally:
        await bot.session.close()
        if user_bot:
            try:
                await user_bot.stop()
            except: pass
        cleanup_task.cancel()
        try:
            await cleanup_task
        except asyncio.CancelledError:
            pass
        await db.close()
        logger.info("Bot to'xtatildi.")


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Bot admin tomonidan to'xtatildi.")
    except Exception as e:
        logger.error("Kutilmagan xato: %s", e)