import telegram
from aiolimiter import AsyncLimiter
from contextlib import contextmanager
from datetime import datetime, timedelta
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from telegram.error import TimedOut, RetryAfter
from telethon import TelegramClient
from telethon.tl.functions.messages import SendReactionRequest
from telethon.tl.types import ReactionEmoji
from collections import defaultdict
from telegram.constants import ChatMemberStatus, ParseMode
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    ContextTypes,
    JobQueue,
    ApplicationBuilder,
    MessageHandler,
    filters
)
import aiohttp
import time
import json
import random
from PIL import Image, ImageDraw, ImageFont
import io
import unicodedata
import re
import requests
import asyncio
import signal
import logging
import sys
import os
import hashlib
import sqlite3
import pytz

# Configure logging
logger = logging.getLogger(__name__)

def setup_logging():
    log_level = os.getenv('PYTHON_LOG_LEVEL', 'INFO').upper()
    log_level = getattr(logging, log_level, logging.INFO)
    logging.basicConfig(
        format='%(asctime)s | %(levelname)s | %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S',
        level=log_level,
        handlers=[
            logging.StreamHandler()  # Direct logs to stdout for systemd
        ]
    )
    # Suppress verbose logs and potential empty lines from external libraries
    for external_logger in ['httpcore', 'httpx', 'telegram', 'telegram.ext', 'telethon', 'apscheduler', 'urllib3']:
        logging.getLogger(external_logger).setLevel(logging.WARNING)
    # Prevent stray empty log messages
    logging.getLogger('').addHandler(logging.NullHandler())

setup_logging()

# Load config.json
try:
    logger.debug("Loading config.json")
    with open("config.json", "r") as file:
        config = json.load(file)
        BOT_TOKEN = config["BOT_TOKEN"]
        API_ID = config["API_ID"]
        API_HASH = config["API_HASH"]
        REPORT_GROUP_ID = config["REPORT_GROUP_ID"]
    logger.debug(f"Successfully loaded config.json with BOT_TOKEN: {BOT_TOKEN[:10]}...")
except Exception as e:
    logger.error(f"Failed to load config.json: {e}")
    sys.exit(1)


# Load banned groups
try:
    logger.debug("Loading banned_groups.json")
    with open("banned_groups.json", "r") as file:
        banned_groups_config = json.load(file)
        BANNED_GROUPS = {group["chat_id"]: group["name"] for group in banned_groups_config["banned_groups"]}
    logger.debug(f"Successfully loaded banned_groups.json with {len(BANNED_GROUPS)} groups")
except Exception as e:
    logger.error(f"Failed to load banned_groups.json: {e}")
    BANNED_GROUPS = {}  # Fallback to empty dict if loading fails

# Load excepted groups
try:
    logger.debug("Loading excepted_groups.json")
    with open("excepted_groups.json", "r") as file:
        excepted_groups_config = json.load(file)
        EXCEPTED_GROUPS = set(excepted_groups_config["excepted_groups"])  # Convert to set for O(1) lookup
    logger.debug(f"Successfully loaded excepted_groups.json with {len(EXCEPTED_GROUPS)} groups")
except Exception as e:
    logger.error(f"Failed to load excepted_groups.json: {e}")
    EXCEPTED_GROUPS = set()  # Fallback to empty set if loading fails
    

# SQLite database file
DB_FILE = "bot_data.db"

# File paths for dynamic leaderboard
GROUPS_PER_SECOND = 30
CHAT_LOCKS = {}
ACHIEVEMENTS_DATA_LOCK = asyncio.Lock()
MAX_PLAYERS = 10  # Show top 10 players
SEND_RATE_LIMITER = AsyncLimiter(GROUPS_PER_SECOND, 1)
GLOBAL_SCHEDULING_LOCK = asyncio.Lock()

# Global variables for data structures
active_questions = {}
quiz_intervals = {}
leaderboard_data = {}
global_leaderboard = {}
streak_data = {}
achievements_data = {}
user_languages = {}
USER_EMOJIS = {}
answer_modes = {}  # Store answer modes for each chat
IMAGE_GEN_SEMAPHORE = asyncio.Semaphore(5)  # Limit to 5 concurrent image generations
BASE_TEMPLATES = {}  # Cache for preloaded leaderboard templates
BASE_STREAK_TEMPLATES = {} # Cache for preloaded streak templates
STREAK_IMAGE_CACHE = {}
LEADERBOARD_IMAGE_CACHE = {}  # Cache for leaderboard images

# Context manager for database connections
@contextmanager
def get_db_connection():
    conn = sqlite3.connect(DB_FILE)
    conn.row_factory = sqlite3.Row  # Allows dictionary-like access to rows
    try:
        yield conn
    finally:
        conn.close()

# Initialize the database with tables
def init_database():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        
        # Leaderboard table (group-specific)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS leaderboard (
                chat_id TEXT,
                user_id TEXT,
                name TEXT,
                score INTEGER,
                PRIMARY KEY (chat_id, user_id)
            )
        """)
        
        # Global leaderboard table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS global_leaderboard (
                user_id TEXT PRIMARY KEY,
                name TEXT,
                score INTEGER
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS global_leaderboard_groups (
                user_id TEXT,
                group_id TEXT,
                group_name TEXT,
                score INTEGER,
                FOREIGN KEY (user_id) REFERENCES global_leaderboard(user_id),
                PRIMARY KEY (user_id, group_id)
            )
        """)
        
        # Streak table (group-specific)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS streaks (
                chat_id TEXT,
                user_id TEXT,
                name TEXT,
                streak INTEGER,
                PRIMARY KEY (chat_id, user_id)
            )
        """)
        
        # Achievements table (remove notified column)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS achievements (
                user_id TEXT,
                achievement_id TEXT,
                PRIMARY KEY (user_id, achievement_id)
            )
        """)
        
        # Enhanced user_stats table to track all necessary metrics
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS user_stats (
                user_id TEXT PRIMARY KEY,
                correct_answers INTEGER DEFAULT 0,
                current_streak INTEGER DEFAULT 0,
                highest_streak INTEGER DEFAULT 0,
                quick_answers INTEGER DEFAULT 0,  -- Answers in under 10 seconds
                taylor_answers INTEGER DEFAULT 0, -- Taylor question answers
                lyrics_answers INTEGER DEFAULT 0, -- Lyrics question answers
                incorrect_answers INTEGER DEFAULT 0, -- Incorrect answers
                groups_participated INTEGER DEFAULT 0, -- Number of groups
                total_points INTEGER DEFAULT 0  -- Total points earned
            )
        """)
        
        # User languages table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS user_languages (
                user_id TEXT PRIMARY KEY,
                language TEXT DEFAULT 'en'
            )
        """)
       
        # Table for user emojis
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS user_emojis (
                user_id TEXT PRIMARY KEY,
                name TEXT,
                emoji TEXT DEFAULT '👤',
                created_at TEXT
            )
        """)
        
        # Group settings table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS group_settings (
                chat_id TEXT PRIMARY KEY,
                group_name TEXT,
                answer_mode TEXT DEFAULT 'buttons',
                quiz_interval INTEGER,
                language TEXT DEFAULT 'en'
            )
        """)
        
        conn.commit()
        logger.info("SQLite database initialized.")

# Load leaderboard data
def load_leaderboard():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT chat_id, user_id, name, score FROM leaderboard")
        rows = cursor.fetchall()
        data = {}
        for row in rows:
            chat_id = row["chat_id"]
            if chat_id not in data:
                data[chat_id] = {"players": {}}
            data[chat_id]["players"][row["user_id"]] = {"name": row["name"], "score": row["score"]}
        return data

# Load global leaderboard data
def load_global_leaderboard():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT user_id, name, score FROM global_leaderboard")
        users = {row["user_id"]: {"name": row["name"], "score": row["score"], "groups": {}} for row in cursor.fetchall()}
        cursor.execute("SELECT user_id, group_id, group_name, score FROM global_leaderboard_groups")
        for row in cursor.fetchall():
            users[row["user_id"]]["groups"][row["group_id"]] = {
                "group_name": row["group_name"],
                "score": row["score"]
            }
        return users

# Load streak data
def load_streak_data():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT chat_id, user_id, name, streak FROM streaks")
        rows = cursor.fetchall()
        data = {}
        for row in rows:
            chat_id = row["chat_id"]
            if chat_id not in data:
                data[chat_id] = {}
            data[chat_id][row["user_id"]] = {"name": row["name"], "streak": row["streak"]}
        return data

def load_user_languages():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT user_id, language FROM user_languages")
        return {row["user_id"]: row["language"] for row in cursor.fetchall()}

# Load achievements from JSON file
with open("achievements.json", "r") as file:
    ACHIEVEMENTS = json.load(file)
        
#Add Functions to Load and Save Achievements Data
def load_achievements_data():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT user_id, achievement_id FROM achievements")
        achievements = cursor.fetchall()
        cursor.execute("""
            SELECT user_id, correct_answers, current_streak, highest_streak,
                   quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                   groups_participated, total_points
            FROM user_stats
        """)
        stats = {row["user_id"]: dict(row) for row in cursor.fetchall()}
        data = {}
        for row in achievements:
            user_id = row["user_id"]
            if user_id not in data:
                data[user_id] = {
                    "correct_answers": stats.get(user_id, {}).get("correct_answers", 0),
                    "current_streak": stats.get(user_id, {}).get("current_streak", 0),
                    "highest_streak": stats.get(user_id, {}).get("highest_streak", 0),
                    "quick_answers": stats.get(user_id, {}).get("quick_answers", 0),
                    "taylor_answers": stats.get(user_id, {}).get("taylor_answers", 0),
                    "lyrics_answers": stats.get(user_id, {}).get("lyrics_answers", 0),
                    "incorrect_answers": stats.get(user_id, {}).get("incorrect_answers", 0),
                    "groups_participated": stats.get(user_id, {}).get("groups_participated", 0),
                    "total_points": stats.get(user_id, {}).get("total_points", 0),
                    "achievements": []
                }
            data[user_id]["achievements"].append(row["achievement_id"])
        for user_id in stats:
            if user_id not in data:
                data[user_id] = {
                    "correct_answers": stats[user_id]["correct_answers"],
                    "current_streak": stats[user_id]["current_streak"],
                    "highest_streak": stats[user_id]["highest_streak"],
                    "quick_answers": stats[user_id]["quick_answers"],
                    "taylor_answers": stats[user_id]["taylor_answers"],
                    "lyrics_answers": stats[user_id]["lyrics_answers"],
                    "incorrect_answers": stats[user_id]["incorrect_answers"],
                    "groups_participated": stats[user_id]["groups_participated"],
                    "total_points": stats[user_id]["total_points"],
                    "achievements": []
                }
        logger.info(f"Loaded achievements_data: {data}")
        return data

# File paths for templates
TEMPLATE_PATHS = {
    "en": "Leaderboard_en.jpg",  # English
    "es": "Leaderboard_es.jpg",  # Spanish
    "ar": "Leaderboard_ar.jpg",  # Arabic
    "fa": "Leaderboard_fa.jpg",  # Persian (Farsi)
    "de": "Leaderboard_de.jpg",  # German
    "fr": "Leaderboard_fr.jpg",  # French
    "it": "Leaderboard_it.jpg",  # Italian
    "pt": "Leaderboard_pt.jpg",  # Portuguese
    "id": "Leaderboard_id.jpg",  # Indonesian
    "ko": "Leaderboard_ko.jpg",  # Korean
    "ru": "Leaderboard_ru.jpg",  # Russian
    "tr": "Leaderboard_tr.jpg",  # Turkish
}

STREAK_TEMPLATE_PATHS = {
    "en": "Streaks_en.jpg",  # English
    "es": "Streaks_es.jpg",  # Spanish
    "ar": "Streaks_ar.jpg",  # Arabic
    "fa": "Streaks_fa.jpg",  # Persian (Farsi)
    "de": "Streaks_de.jpg",  # German
    "fr": "Streaks_fr.jpg",  # French
    "it": "Streaks_it.jpg",  # Italian
    "pt": "Streaks_pt.jpg",  # Portuguese
    "id": "Streaks_id.jpg",  # Indonesian
    "ko": "Streaks_ko.jpg",  # Korean
    "ru": "Streaks_ru.jpg",  # Russian
    "tr": "Streaks_tr.jpg",  # Turkish
}

# File paths for dynamic leaderboard
FONT_PATHS = {
    "ja": "NotoSansJP-ExtraBold.ttf",  # Japanese
    "ko": "NotoSansKR-ExtraBold.ttf",  # Korean
    "en": "NotoSans-ExtraBold.ttf",    # English and other languages
    "ar": "NotoNaskhArabic-Bold.ttf"  # Arabic
}

# File paths for profile name
FONT_PATHS2 = {
    "jap": "NotoSansJP-ExtraBold.ttf",  # Japanese
    "kor": "NotoSansKR-ExtraBold.ttf",  # Korean
    "eng": "NotoSans-ExtraBold.ttf",    # English and other languages
    "ara": "NotoNaskhArabic-Bold.ttf"  # Arabic
}

RANDOM_EMOJIS = ["🎉", "👀","🤩","😎", "😍", "🔥", "💯", "🍾", "🏆", "❤️‍🔥", "👌", "⚡", "🦄"]

AVAILABLE_EMOJIS = [
    "🦸🏻", "🦸🏻‍♂️", "🦸🏻‍♀️", "🧑🏻‍🎤",
    "👨🏻‍🎤", "👩🏻‍🎤","🦹🏻", "🦹🏻‍♂️",
    "🦹🏻‍♀️", "🧑🏻‍🚀", "👨🏻‍🚀", "👩🏻‍🚀",
    "🤴🏻", "👸🏻", "🧕🏻","🧟",
    "🧟‍♂️", "🧟‍♀️","🕵🏻", "🕵🏻‍♂️",
      "🕵🏻‍♀️","🧑🏻‍⚖️", "👨🏻‍⚖️", "👩🏻‍⚖️",
    "🤵🏻", "🤵🏻‍♂️", "🤵🏻‍♀️","🧑🏻‍💻",
    "👨🏻‍💻", "👩🏻‍💻", "🧑🏻‍⚕️", "👨🏻‍⚕️",
    "👩🏻‍⚕️","🧑🏻‍💼", "👨🏻‍💼", "👩🏻‍💼",
]

LANGUAGE_FLAGS = {
    "en": "🇺🇸",  # English (US flag as a common representation)
    "es": "🇪🇸",  # Spanish
    "ar": "🇸🇦",  # Arabic (Saudi Arabia flag as a common representation)
    "fa": "🇮🇷",  # Persian (Farsi)
    "de": "🇩🇪",  # German
    "fr": "🇫🇷",  # French
    "it": "🇮🇹",  # Italian
    "pt": "🇵🇹",  # Portuguese
    "id": "🇮🇩",  # Indonesian
    "ko": "🇰🇷",  # Korean
    "ru": "🇷🇺",  # Russian
    "tr": "🇹🇷",  # Turkish
}

# Load quiz data from two separate files
try:
    with open("lyrics_questions.json", "r", encoding="utf-8") as file:
        lyrics_questions = json.load(file)
    logger.info("Successfully loaded lyrics_questions.json with UTF-8 encoding")
except Exception as e:
    logger.error(f"Failed to load lyrics_questions.json: {e}")
    lyrics_questions = []  # Fallback to empty list if loading fails

try:
    with open("taylor_questions.json", "r", encoding="utf-8") as file:
        taylor_questions = json.load(file)
    logger.info("Successfully loaded taylor_questions.json with UTF-8 encoding")
except Exception as e:
    logger.error(f"Failed to load taylor_questions.json: {e}")
    taylor_questions = []  # Fallback to empty list if loading fails
    

# Load localization data
with open("localization.json", "r", encoding="utf-8") as file:
    localization = json.load(file)

async def save_user_languages(data):
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("DELETE FROM user_languages")
        for user_id, language in data.items():
            cursor.execute("""
                INSERT OR REPLACE INTO user_languages (user_id, language)
                VALUES (?, ?)
            """, (user_id, language))
        conn.commit()
        logger.info("User languages saved to SQLite.")

def load_user_emojis():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT user_id, name, emoji FROM user_emojis")
        rows = cursor.fetchall()
        user_emojis = {row["user_id"]: {"name": row["name"], "emoji": row["emoji"]} for row in rows}
        logger.info(f"Loaded {len(user_emojis)} user emojis from SQLite.")
        return user_emojis

def get_emoji_for_user(user_id):
    """Returns an emoji based on the user's ID."""
    user_id_str = str(user_id)
    user_data = USER_EMOJIS.get(user_id_str)
    if user_data:
        return user_data["emoji"]
    return "👤"  # Default emoji from the table

#save user emoji
async def save_user_emoji(user_id: str, name: str, emoji: str):
    """Save or update a user's emoji in the database."""
    global USER_EMOJIS
    timestamp = datetime.now().isoformat()  # Store timestamp in ISO format
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("""
            INSERT INTO user_emojis (user_id, name, emoji, created_at)
            VALUES (?, ?, ?, ?)
            ON CONFLICT(user_id) DO UPDATE SET
                name = excluded.name,
                emoji = excluded.emoji,
                created_at = excluded.created_at
        """, (user_id, name, emoji, timestamp))
        conn.commit()
    USER_EMOJIS[user_id] = {"name": name, "emoji": emoji, "created_at": timestamp}
    logger.debug(f"Saved emoji {emoji} for user {user_id}")
    
#checks valid image url
def is_valid_image_url(url):
    try:
        response = requests.head(url, allow_redirects=True)
        if response.status_code == 200:
            content_type = response.headers.get("Content-Type", "").lower()
            return content_type.startswith("image/")
        return False
    except Exception as e:
        logger.error(f"Error checking image URL: {e}")
        return 
    
def get_total_users():
    """Count unique users who have interacted with the bot."""
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("""
            SELECT COUNT(DISTINCT user_id) as total_users FROM (
                SELECT user_id FROM user_stats
                UNION
                SELECT user_id FROM user_languages
                UNION
                SELECT user_id FROM user_emojis
                UNION
                SELECT user_id FROM global_leaderboard
                UNION
                SELECT user_id FROM achievements
            )
        """)
        result = cursor.fetchone()
        total_users = result["total_users"] if result else 0
        logger.info(f"Calculated total users: {total_users}")
        return total_users

def get_total_groups():
    """Count total groups the bot is in, based on group_settings."""
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT COUNT(*) as total_groups FROM group_settings")
        result = cursor.fetchone()
        total_groups = result["total_groups"] if result else 0
        logger.info(f"Calculated total groups: {total_groups}")
        return total_groups
    
#Check for memebers count
async def can_bot_operate(chat_id: str, context: ContextTypes.DEFAULT_TYPE) -> tuple[bool, str]:
    """
    Check if the bot can operate in the group based on member count or exception list.
    Returns: (can_operate: bool, message: str)
    """
    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    if chat_id in EXCEPTED_GROUPS:
        return True, ""  # Excepted group, allow operation

    try:
        chat = await context.bot.get_chat(chat_id)
        member_count = await context.bot.get_chat_member_count(chat_id)
        # Subtract 1 to exclude the bot itself
        member_count -= 1
        if member_count >= 15:
            return True, ""
        else:
            return False, localized["min_members_required"].format(required=15, current=member_count)
    except Exception as e:
        logger.error(f"Error checking member count for chat {chat_id}: {e}")
        return False, localized["generic_error"]
    
# Function to preload templates (add after existing global variables)
def load_templates():
    for lang, path in TEMPLATE_PATHS.items():
        try:
            BASE_TEMPLATES[lang] = Image.open(path)
            logger.info(f"Loaded leaderboard template for {lang}")
        except FileNotFoundError:
            logger.error(f"Leaderboard template not found: {path}")
    for lang, path in STREAK_TEMPLATE_PATHS.items():
        try:
            BASE_STREAK_TEMPLATES[lang] = Image.open(path)
            logger.info(f"Loaded streak template for {lang}")
        except FileNotFoundError:
            logger.error(f"Streak template not found: {path}")
    
    
# Initialize Telethon client
client = TelegramClient("bot_session", API_ID, API_HASH)
    
API_URL = f"https://api.telegram.org/bot{BOT_TOKEN}/setMyCommands"

def set_bot_commands():
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/setMyCommands"

    # Commands for private chats (exclude /stats)
    private_commands = [
        {"command": "start", "description": "Start the Bot"}
    ]

    # Commands for all group chats (exclude /stats)
    group_commands = [
        {"command": "leaderboard", "description": "View the leaderboard"},
        {"command": "settings", "description": "(ADMINS) Configure group settings"},
        {"command": "streak", "description": "View streaks data"},
        {"command": "profile", "description": "View your stats"},
        {"command": "reportquestion", "description": "Report an incorrect question"}
    ]

    # Commands for the specific group (include /stats)
    specific_group_commands = [
        {"command": "leaderboard", "description": "View the leaderboard"},
        {"command": "settings", "description": "(ADMINS) Configure group settings"},
        {"command": "streak", "description": "View streaks data"},
        {"command": "profile", "description": "View your stats"},
        {"command": "reportquestion", "description": "Report an incorrect question"},
        {"command": "stats", "description": "(ADMINS) View bot statistics"}
    ]

    # Set commands for private chats
    private_payload = {
        "commands": private_commands,
        "scope": {"type": "all_private_chats"}
    }
    response_private = requests.post(url, json=private_payload)
    if response_private.status_code == 200:
        logger.info("Private chat commands set successfully!")
    else:
        logger.error(f"Failed to set private chat commands: {response_private.text}")

    # Set commands for all group chats
    group_payload = {
        "commands": group_commands,
        "scope": {"type": "all_group_chats"}
    }
    response_group = requests.post(url, json=group_payload)
    if response_group.status_code == 200:
        logger.info("Group chat commands set successfully!")
    else:
        logger.error(f"Failed to set group chat commands: {response_group.text}")

    # Set commands for the specific group
    specific_group_payload = {
        "commands": specific_group_commands,
        "scope": {
            "type": "chat",
            "chat_id": REPORT_GROUP_ID
        }
    }
    response_specific = requests.post(url, json=specific_group_payload)
    if response_specific.status_code == 200:
        logger.info(f"Commands set successfully for specific group {REPORT_GROUP_ID}!")
    else:
        logger.error(f"Failed to set commands for specific group {REPORT_GROUP_ID}: {response_specific.text}")
       
#valid url with https      
def is_valid_url(url):
    return url.startswith("https://")

#next interval time
def get_next_interval_time(interval_seconds):
    """Calculate the delay until the next full hour UTC time (e.g., 1:00, 2:00) based on interval."""
    utc_now = datetime.now(pytz.utc)  # Current UTC time
    current_hour = utc_now.hour
    current_minutes = utc_now.minute
    current_seconds = utc_now.second

    # Calculate seconds since the start of the current hour
    seconds_since_hour_start = (current_minutes * 60) + current_seconds

    # Interval in hours (assuming interval_seconds is always a multiple of 3600)
    interval_hours = interval_seconds // 3600

    # Find the next full hour that aligns with the interval
    next_hour = ((current_hour // interval_hours) + 1) * interval_hours
    next_hour = next_hour % 24  # Wrap around to 0-23 hours

    # Calculate the next UTC datetime at the full hour
    next_time_utc = utc_now.replace(minute=0, second=0, microsecond=0)
    if next_hour <= current_hour and seconds_since_hour_start > 0:
        # If the next hour is today but already passed, move to the next day
        next_time_utc = next_time_utc + timedelta(days=1)
        next_time_utc = next_time_utc.replace(hour=next_hour)
    else:
        next_time_utc = next_time_utc.replace(hour=next_hour)

    # Calculate delay in seconds
    delay = (next_time_utc - utc_now).total_seconds()
    if delay < 0:  # Shouldn't happen, but just in case
        delay += 86400  # Add a day if somehow negative

    return delay

# Load group settings from JSON file
def load_group_settings():
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("SELECT chat_id, group_name, answer_mode, quiz_interval, language FROM group_settings")
        return {row["chat_id"]: dict(row) for row in cursor.fetchall()}

async def save_group_settings(data):
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("DELETE FROM group_settings")
        for chat_id, settings in data.items():
            cursor.execute("""
                INSERT OR REPLACE INTO group_settings (chat_id, group_name, answer_mode, quiz_interval, language)
                VALUES (?, ?, ?, ?, ?)
            """, (chat_id, settings["group_name"], settings["answer_mode"], settings["quiz_interval"], settings["language"]))
        conn.commit()
        logger.info("Group settings saved to SQLite.")
        return True
        
# Dictionary to track user activity
user_activity = defaultdict(dict)

# Rate limit settings (e.g., 1 command per 5 seconds)
RATE_LIMIT = 10  # Seconds between commands

#Emoji Callback
async def emoji_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global USER_EMOJIS
    query = update.callback_query
    data = query.data
    user_id = str(query.from_user.id)
    chat_id = str(query.message.chat_id)
    first_name = query.from_user.first_name
    bot_username = context.bot.username

    try:
        user_language = user_languages.get(user_id, "en")
        localized = localization.get(user_language, localization["en"])

        if data == "emoji_select":
            current_emoji = USER_EMOJIS.get(user_id, {}).get("emoji", "👤")
            keyboard = []
            title_text = localized.get('emoji_selection_title')
            prompt_text = localized.get('emoji_selection_prompt')
            message_text = f"{title_text}\n{prompt_text}"
            for i in range(0, len(AVAILABLE_EMOJIS), 4):
                row = [
                    InlineKeyboardButton(
                        f"{emoji} {'🔘' if emoji == current_emoji else ''}",
                        callback_data=f"set_emoji_{emoji}"
                    ) for emoji in AVAILABLE_EMOJIS[i:i+4]
                ]
                keyboard.append(row)
            keyboard.append([InlineKeyboardButton(localized["back_button"], callback_data="emoji_back")])
            reply_markup = InlineKeyboardMarkup(keyboard)
            # Set the title and prompt as the message text
            await query.edit_message_text(
                text=message_text,
                reply_markup=reply_markup,
                parse_mode="HTML",
                disable_web_page_preview=False
            )

        elif data.startswith("set_emoji_"):
            emoji = data.replace("set_emoji_", "")
            if emoji in AVAILABLE_EMOJIS:
                await save_user_emoji(user_id, first_name, emoji)
                keyboard = []
                title_text = localized.get('emoji_selection_title')
                prompt_text = localized.get('emoji_selection_prompt')
                message_text = f"{title_text}\n{prompt_text}"
                for i in range(0, len(AVAILABLE_EMOJIS), 4):
                    row = [
                        InlineKeyboardButton(
                            f"{e} {'🔘' if e == emoji else ''}",
                            callback_data=f"set_emoji_{e}"
                        ) for e in AVAILABLE_EMOJIS[i:i+4]
                    ]
                    keyboard.append(row)
                keyboard.append([InlineKeyboardButton(localized["back_button"], callback_data="emoji_back")])
                reply_markup = InlineKeyboardMarkup(keyboard)
                # Set the title and prompt as the message text
                await query.edit_message_text(
                    text=message_text,
                    reply_markup=reply_markup,
                    parse_mode="HTML",
                    disable_web_page_preview=False
                )

        elif data == "emoji_back":
            caption = localized["welcome"].format(
                first_name=first_name,
                user_id=user_id
            )
            keyboard = [
                [InlineKeyboardButton(localized["add_to_group"], url=f"https://t.me/{bot_username}?startgroup=true")],
                [InlineKeyboardButton(localized["support"], url="https://t.me/MastermindBotSupport"),
                 InlineKeyboardButton(localized["updates"], url="https://t.me/MastermindBotUpdates")],
                [InlineKeyboardButton(localized["language"], callback_data="language_select"),
                 InlineKeyboardButton(localized.get("emoji_select_button"), callback_data="emoji_select")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            # Update the message text and keyboard for the back action
            await query.edit_message_text(
                text=caption,
                reply_markup=reply_markup,
                parse_mode="HTML"
            )

        elif data == "no_action":
            await query.answer()

    except Exception as e:
        logger.error(f"Error in emoji_callback: {e}")
        await query.answer(f"❌ An error occurred: {str(e)}", show_alert=True)

#sanitize inputs
def sanitize_input(text):
    if not text:
        return ""
    # Remove HTML tags
    sanitized_text = re.sub(r"<[^>]+>", "", text)
    # Keep alphanumeric characters, spaces, and minimal punctuation (.,!?)
    sanitized_text = re.sub(r"[^\w\s.,!?]", "", sanitized_text)
    # Normalize spaces but preserve multi-word structure
    sanitized_text = " ".join(sanitized_text.split())
    return sanitized_text.strip()

async def save_achievements_data(data):
    async with ACHIEVEMENTS_DATA_LOCK:
        with get_db_connection() as conn:
            cursor = conn.cursor()
            for user_id, user_data in data.items():
                cursor.execute("""
                    INSERT INTO user_stats (
                        user_id, correct_answers, current_streak, highest_streak,
                        quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                        groups_participated, total_points
                    )
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(user_id) DO UPDATE SET
                        correct_answers = excluded.correct_answers,
                        current_streak = excluded.current_streak,
                        highest_streak = excluded.highest_streak,
                        quick_answers = excluded.quick_answers,
                        taylor_answers = excluded.taylor_answers,
                        lyrics_answers = excluded.lyrics_answers,
                        incorrect_answers = excluded.incorrect_answers,
                        groups_participated = excluded.groups_participated,
                        total_points = excluded.total_points
                """, (
                    user_id,
                    user_data["correct_answers"],
                    user_data["current_streak"],
                    user_data["highest_streak"],
                    user_data["quick_answers"],
                    user_data["taylor_answers"],
                    user_data["lyrics_answers"],
                    user_data["incorrect_answers"],
                    user_data["groups_participated"],
                    user_data["total_points"]
                ))
                # Delete existing achievements for user
                cursor.execute("DELETE FROM achievements WHERE user_id = ?", (user_id,))
                # Insert current achievements
                for ach_id in user_data["achievements"]:
                    cursor.execute("""
                        INSERT OR REPLACE INTO achievements (user_id, achievement_id)
                        VALUES (?, ?)
                    """, (user_id, ach_id))
            conn.commit()
        logger.info("Achievements data saved to SQLite.")
              
#Global Rank Calculation
def get_global_rank(user_id):
    global_leaderboard = load_global_leaderboard()
    sorted_players = sorted(
        global_leaderboard.items(),
        key=lambda x: x[1]["score"],  # Use total score
        reverse=True
    )
    for rank, (uid, _) in enumerate(sorted_players, start=1):
        if uid == str(user_id):
            return rank
    return None

# Function to check rate limits
def is_rate_limited(user_id, action):
    current_time = time.time()
    last_action_time = user_activity[user_id].get(action, 0)

    if current_time - last_action_time < RATE_LIMIT:
        return True  # User is rate-limited
    else:
        user_activity[user_id][action] = current_time  # Update last action time
        return False  # User is not rate-limited

# Timeout handling
async def send_message_with_retry(chat_id, text, retries=3):
    async with SEND_RATE_LIMITER:
        for attempt in range(retries):
            try:
                await application.bot.send_message(chat_id=chat_id, text=text)
                return True
            except RetryAfter as e:
                delay = e.retry_after if e.retry_after else 2 ** attempt
                logger.warning(f"Rate limit hit: {e}. Retrying in {delay}s...")
                await asyncio.sleep(delay)
            except TimedOut:
                if attempt < retries - 1:
                    await asyncio.sleep(1)
                else:
                    logger.error(f"Failed to send message after {retries} attempts.")
                    return False
        logger.error(f"Failed to send message after {retries} attempts due to rate limits.")
        return False
                
#reset leaderboard
async def reset_leaderboard(chat_id):
    global leaderboard_data
    chat_id_str = str(chat_id)
    leaderboard_data[chat_id_str] = {"players": {}}
    await save_leaderboard(leaderboard_data)
    logger.info(f"Leaderboard reset for chat {chat_id_str}")
    return True

# Increase connection pool size and timeout settings
application = (
    ApplicationBuilder()
    .token(BOT_TOKEN)
    .read_timeout(30)
    .write_timeout(30)
    .connect_timeout(30)
    .connection_pool_size(20)
    .pool_timeout(20)
    .build()
)

# Save streak data
async def save_streak_data(data):
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("DELETE FROM streaks")
        for chat_id, chat_data in data.items():
            for user_id, user_data in chat_data.items():
                cursor.execute("""
                    INSERT OR REPLACE INTO streaks (chat_id, user_id, name, streak)
                    VALUES (?, ?, ?, ?)
                """, (chat_id, user_id, user_data["name"], user_data["streak"]))
        conn.commit()
        logger.info("Streak data saved to SQLite.")
        return True

# Function to add a reaction using the Telegram Bot API
async def add_reaction_bot(chat_id, message_id, emoji="🎉", is_big=True):
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/setMessageReaction"
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reaction": [{"type": "emoji", "emoji": emoji, "is_big": is_big}]
    }
    async with aiohttp.ClientSession() as session:
        async with session.post(url, json=payload) as response:
            if response.status == 200:
                logger.info(f"Reaction added as bot: {emoji} (Big: {is_big})")
            else:
                logger.error(f"Failed to add reaction: {await response.text()}")

#Start Command
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle the /start command, initialize user data, and send welcome message."""
    if update.message.chat.type != "private":
        return  # Ignore if not in private chat

    user_id = str(update.message.from_user.id)  # Ensure user_id is a string
    chat_id = update.message.chat_id
    bot_username = context.bot.username
    first_name = update.message.from_user.first_name  # Get user's first name (e.g., Hafeel)

    # Insert or update user language in the database
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute(
            "INSERT OR IGNORE INTO user_languages (user_id, language) VALUES (?, ?)",
            (user_id, "en")
        )
        conn.commit()

    # Update global user_languages dictionary
    global user_languages
    user_languages[user_id] = "en"  # Set default language
    user_language = user_languages.get(user_id, "en")  # Default to English

    # Get localized strings
    localized = localization.get(user_language, localization["en"])  # Default to English if language not found

    # Format the welcome message with first_name and user_id
    caption = localized["welcome"].format(
        first_name=first_name,
        user_id=user_id
    )

    # Buttons
    keyboard = [
        [InlineKeyboardButton(localized["add_to_group"], url=f"https://t.me/{bot_username}?startgroup=true")],
        [InlineKeyboardButton(localized["support"], url="https://t.me/MastermindBotSupport"),
         InlineKeyboardButton(localized["updates"], url="https://t.me/MastermindBotUpdates")],
        [InlineKeyboardButton(localized["language"], callback_data="language_select"),
         InlineKeyboardButton(localized.get("emoji_select_button"), callback_data="emoji_select")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    # Send the welcome message
    await context.bot.send_message(
        chat_id=chat_id,
        text=caption,
        parse_mode="HTML",
        reply_markup=reply_markup,
        disable_web_page_preview=False
    )

#Stats Command
async def stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Display total users and groups the bot is in, only in the specific group."""
    user_id = str(update.message.from_user.id)
    chat_id = str(update.message.chat_id)
    chat_type = update.message.chat.type

    # Load group settings to get language
    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Check if the command is executed in the specific group
    if chat_type not in ["group", "supergroup"] or chat_id != REPORT_GROUP_ID:
        await update.message.reply_text(localized["stats_unauthorized"], parse_mode=ParseMode.HTML)
        logger.info(f"User {user_id} attempted /stats in unauthorized chat {chat_id}")
        return

    # Check if the user is an admin in the specific group
    chat_member = await context.bot.get_chat_member(chat_id, user_id)
    if chat_member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
        await update.message.reply_text(localized["admin_only"], parse_mode=ParseMode.HTML)
        logger.info(f"Non-admin user {user_id} attempted /stats in chat {chat_id}")
        return

    # Get totals
    total_users = get_total_users()
    total_groups = get_total_groups()

    # Format the response
    message = localized.get("stats_message", "📊 Bot Statistics\n\n👤 Total Users: {users}\n🏠 Total Groups: {groups}")
    message = message.format(users=total_users, groups=total_groups)

    try:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        logger.info(f"Sent stats to user {user_id} in chat {chat_id}: {total_users} users, {total_groups} groups")
    except Exception as e:
        logger.error(f"Failed to send stats to chat {chat_id}: {e}")
        await update.message.reply_text(localized["generic_error"], parse_mode=ParseMode.HTML)
                
# SEND QUESTION
async def send_question(context: ContextTypes.DEFAULT_TYPE):
    chat_id = str(context.job.chat_id)
    logger.info(f"send_question triggered for chat {chat_id}, job name: {context.job.name}, at {datetime.now(pytz.utc)}")
    
    # Check if bot can operate
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        logger.info(f"Cannot send question to chat {chat_id}: {message}")
        # Notify the group and stop the job
        try:
            await context.bot.send_message(
                chat_id=chat_id,
                text=message,
                parse_mode=ParseMode.HTML
            )
            logger.info(f"Sent minimum members message to chat {chat_id}")
        except Exception as e:
            logger.error(f"Failed to send minimum members message to chat {chat_id}: {e}")
        # Remove scheduled jobs for this chat
        current_jobs = context.job_queue.get_jobs_by_name(f"send_{chat_id}") + \
                       context.job_queue.get_jobs_by_name(f"send_{chat_id}_first")
        for job in current_jobs:
            job.schedule_removal()
            logger.info(f"Removed job {job.name} for chat {chat_id}")
        # Disable quiz interval to prevent further attempts
        group_settings = load_group_settings()
        if chat_id in group_settings:
            group_settings[chat_id]["quiz_interval"] = None
            await save_group_settings(group_settings)
            logger.info(f"Disabled quiz interval for chat {chat_id}")
        return

    # Initialize lock for this chat if not present
    if chat_id not in CHAT_LOCKS:
        CHAT_LOCKS[chat_id] = asyncio.Lock()

    async with CHAT_LOCKS[chat_id]:  # Ensure only one send at a time
        group_settings = load_group_settings()
        if chat_id not in group_settings or not group_settings[chat_id].get("quiz_interval"):
            logger.warning(f"No valid settings or interval for chat {chat_id}, skipping")
            return

        # Check if the bot is still a member of the group
        try:
            bot_id = context.bot.id
            chat_member = await context.bot.get_chat_member(chat_id, bot_id)
            if chat_member.status not in [ChatMemberStatus.MEMBER, ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
                logger.warning(f"Bot is not a member of chat {chat_id} (status: {chat_member.status}), removing jobs and settings")
                # Remove scheduled jobs
                current_jobs = context.job_queue.get_jobs_by_name(f"send_{chat_id}") + \
                               context.job_queue.get_jobs_by_name(f"send_{chat_id}_first")
                for job in current_jobs:
                    job.schedule_removal()
                    logger.info(f"Removed job {job.name} for chat {chat_id}")
                # Remove group settings
                if chat_id in group_settings:
                    del group_settings[chat_id]
                    await save_group_settings(group_settings)
                    logger.info(f"Removed group settings for chat {chat_id}")
                return
        except telegram.error.Forbidden as e:
            logger.error(f"Bot is likely kicked from chat {chat_id}: {e}")
            # Remove scheduled jobs
            current_jobs = context.job_queue.get_jobs_by_name(f"send_{chat_id}") + \
                           context.job_queue.get_jobs_by_name(f"send_{chat_id}_first")
            for job in current_jobs:
                job.schedule_removal()
                logger.info(f"Removed job {job.name} for chat {chat_id}")
            # Remove group settings
            if chat_id in group_settings:
                del group_settings[chat_id]
                await save_group_settings(group_settings)
                logger.info(f"Removed group settings for chat {chat_id}")
            return
        except Exception as e:
            logger.error(f"Error checking membership in chat {chat_id}: {e}")
            return

        group_language = group_settings[chat_id].get("language", "en")
        localized = localization.get(group_language, localization["en"])
        answer_mode = group_settings[chat_id].get("answer_mode", "buttons")

        # Keep trying until a question is successfully sent
        while True:
            question_data = None
            questions_tried = set()
            question_type = random.choice(["lyrics", "taylor"])
            question_pool = lyrics_questions if question_type == "lyrics" else taylor_questions

            # Try all questions in the current pool
            while len(questions_tried) < len(question_pool):
                question = random.choice([q for q in question_pool if id(q) not in questions_tried])
                questions_tried.add(id(question))
                image_url = question["image"]
                if is_valid_url(image_url) and is_valid_image_url(image_url):
                    question_data = {
                        "image": image_url,
                        "options": question["options"].copy(),
                        "correct_answers": [ans.lower() for ans in question["answer"]],
                        "type": question_type,
                        "caption": localized["lyrics_prompt"] if question_type == "lyrics" else localized["taylor_prompt"],
                        "question_number": question.get("questionnumber", "Unknown")
                    }
                    logger.info(f"Selected valid question for chat {chat_id}: {image_url}, question_number: {question_data['question_number']}")
                    break
                else:
                    logger.warning(f"Invalid image URL for chat {chat_id}: {image_url}")

            # If no valid question found in the current pool, switch question type and retry
            if not question_data:
                question_type = "taylor" if question_type == "lyrics" else "lyrics"
                question_pool = lyrics_questions if question_type == "lyrics" else taylor_questions
                questions_tried.clear()
                logger.info(f"No valid question found in {question_type} pool for chat {chat_id}, switching to {question_type}")
                continue

            # Send the question with retries
            async with SEND_RATE_LIMITER:
                for attempt in range(3):
                    try:
                        if answer_mode == "buttons":
                            random.shuffle(question_data["options"])
                            buttons = [[InlineKeyboardButton(f"›› {opt}", callback_data=f"answer_{opt.lower()}")] for opt in question_data["options"]]
                            reply_markup = InlineKeyboardMarkup(buttons)
                        else:
                            reply_markup = None

                        message = await context.bot.send_photo(
                            chat_id=chat_id,
                            photo=question_data["image"],
                            caption=question_data["caption"],
                            parse_mode="HTML",
                            reply_markup=reply_markup,
                            protect_content=True,
                            has_spoiler=True,
                            read_timeout=30,
                            write_timeout=30,
                            connect_timeout=30
                        )
                        logger.info(f"Successfully sent question to chat {chat_id} on attempt {attempt + 1}")

                        question_key = f"{chat_id}_{message.message_id}"
                        active_questions[question_key] = {
                            "chat_id": chat_id,
                            "correct_answers": question_data["correct_answers"],
                            "start_time": time.time(),
                            "type": question_data["type"],
                            "answered": False,
                            "message_id": message.message_id,
                            "question_number": question_data["question_number"]
                        }

                        context.job_queue.run_once(
                            send_alarm,
                            300,
                            chat_id=chat_id,
                            name=f"alarm_{question_key}",
                            data={"question_key": question_key}
                        )
                        context.job_queue.run_once(
                            update_caption,
                            600,
                            chat_id=chat_id,
                            name=f"timeup_{question_key}",
                            data={"question_key": question_key}
                        )
                        return
                    except telegram.error.Forbidden as e:
                        logger.error(f"Forbidden error on attempt {attempt + 1} for chat {chat_id}: {e}")
                        # Assume bot was kicked, clean up jobs and settings
                        current_jobs = context.job_queue.get_jobs_by_name(f"send_{chat_id}") + \
                                       context.job_queue.get_jobs_by_name(f"send_{chat_id}_first")
                        for job in current_jobs:
                            job.schedule_removal()
                            logger.info(f"Removed job {job.name} for chat {chat_id}")
                        if chat_id in group_settings:
                            del group_settings[chat_id]
                            await save_group_settings(group_settings)
                            logger.info(f"Removed group settings for chat {chat_id}")
                        return
                    except Exception as e:
                        logger.error(f"Failed to send to chat {chat_id} on attempt {attempt + 1}: {e}")
                        if attempt < 2:
                            await asyncio.sleep(2 ** attempt)
                        else:
                            logger.warning(f"All send attempts failed for chat {chat_id}, retrying with a new question")
                            break
                        
#Scheldule Quiz Jobs
async def schedule_quiz_jobs(job_queue, chat_id: str, interval: int):
    chat_id = str(chat_id)
    # Remove existing jobs
    for name in [f"send_{chat_id}", f"send_{chat_id}_first"]:
        for job in job_queue.get_jobs_by_name(name):
            job.schedule_removal()
            logger.info(f"Removed job {name} for chat {chat_id}")
    # Schedule new jobs
    delay = get_next_interval_time(interval)
    job_queue.run_once(
        send_question,
        when=delay,
        chat_id=int(chat_id),
        name=f"send_{chat_id}_first"
    )
    job_queue.run_repeating(
        send_question,
        interval=interval,
        first=delay + interval,
        chat_id=int(chat_id),
        name=f"send_{chat_id}"
    )
    logger.info(f"Scheduled jobs for chat {chat_id}: first in {delay}s, interval {interval}s")

#ALARM SYSTEM
async def send_alarm(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    question_key = job.data["question_key"]

    if question_key in active_questions:
        question_data = active_questions[question_key]
        if not question_data["answered"]:
            group_settings = load_group_settings()
            group_language = group_settings.get(str(chat_id), {}).get("language", "en")
            localized = localization.get(group_language, localization["en"])

            try:
                message = await context.bot.send_message(
                    chat_id=chat_id,
                    text=localized["alarm"],
                    reply_to_message_id=question_data["message_id"],
                    disable_notification=True  #AVOID EXCESSIVE NOTIFICATIONS
                )
                question_data["alarm_message_id"] = message.message_id
                logger.info(f"Alarm message sent with ID {message.message_id} for question {question_key}")
            except Exception as e:
                logger.error(f"Failed to send alarm message for question {question_key}: {e}")
                success = await send_message_with_retry(
                    chat_id=chat_id,
                    text=localized["alarm"],
                    retries=3
                )
                if success:
                    logger.info(f"Alarm message sent via retry for question {question_key}")
                else:
                    logger.warning(f"Failed to send alarm message for question {question_key} after retries")


# UPDATED UPDATE_CAPTION FUNCTION
async def update_caption(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    question_key = job.data.get("question_key")  # GET FROM DATA INSTEAD OF NAME

    if not question_key:
        logger.error(f"No question_key provided in job data for timeup job")
        return

    if question_key not in active_questions:
        logger.info(f"No active question found for key {question_key} in update_caption")
        return

    question_data = active_questions[question_key]
    chat_id = question_data["chat_id"]

    if question_data["answered"]:
        logger.info(f"Question already answered for key {question_key}, skipping caption update")
        return

    message_id = question_data.get("message_id")
    question_type = question_data["type"]

    if not message_id:
        logger.error(f"No message_id found for question {question_key}")
        return

    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    try:
        caption = localized["lyrics_time_up"] if question_type == "lyrics" else localized["taylor_time_up"]
        await context.bot.edit_message_caption(
            chat_id=chat_id,
            message_id=message_id,
            caption=caption,
            parse_mode=ParseMode.HTML,
            reply_markup=None
        )
        logger.info(f"Caption updated to 'Times Up' for question {question_key}")
    except telegram.error.BadRequest as e:
        logger.error(f"Failed to update caption for question {question_key}: {e}")
        return

    if "alarm_message_id" in question_data:
        alarm_message_id = question_data["alarm_message_id"]
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=alarm_message_id)
            logger.info(f"Alarm message {alarm_message_id} deleted for question {question_key}")
            del question_data["alarm_message_id"]
        except telegram.error.BadRequest as e:
            logger.error(f"Failed to delete alarm message {alarm_message_id} for question {question_key}: {e}")

    question_data["answered"] = True
    context.job_queue.run_once(
        delete_unanswered_question,
        when=180,
        chat_id=chat_id,
        data={"question_key": question_key}
    )

# DELETE UNANSWERED QUESTIONS AFTER 3 MINUTES
async def delete_unanswered_question(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    question_key = job.data["question_key"]

    if question_key in active_questions:
        question_data = active_questions[question_key]
        message_id = question_data.get("message_id")
        try:
            if message_id:
                await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
                logger.info(f"Unanswered question {message_id} deleted for key {question_key}")
        except Exception as e:
            logger.error(f"Failed to delete message for question {question_key}: {e}")

        # CLEAN UP THE ACTIVE_QUESTIONS DICTIONARY USING THE QUESTION_KEY
        del active_questions[question_key]
        logger.info(f"Cleaned up active_questions entry for key {question_key}")
    else:
        logger.info(f"No active question found for key {question_key} at deletion time")

#Log active jobs        
async def log_active_jobs(job_queue):
    while True:
        jobs = job_queue.scheduler.get_jobs()  # Get jobs directly from APScheduler
        logger.info(f"Active jobs: {len(jobs)}")
        for job in jobs:
            try:
                next_run = job.next_run_time if job.next_run_time else "Pending"
                logger.info(f"Job: {job.name}, next run: {next_run}")
            except Exception as e:
                logger.error(f"Error logging job {job.name}: {e}")
        await asyncio.sleep(3600)  # Log every hour

#DELETE MESSAGE FUNCTION
async def delete_message(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    message_id = job.data["message_id"]

    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception as e:
        logger.error(f"Failed to delete message: {e}")

# HANDLE ANSWER AND UPDATE GLOBAL LEADERBOARD
async def handle_answer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    if not data.startswith("answer_"):
        await query.answer("❌ Invalid input.")
        return
    chat_id = query.message.chat_id
    user_id = query.from_user.id
    user_name = query.from_user.first_name
    selected_answer = data.split("_")[1]
    question_key = f"{chat_id}_{query.message.message_id}"
    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    await save_user_emoji(user_id, user_name)

    if question_key not in active_questions:
        await query.answer("⏳ Time's up! No more answers accepted.")
        return

    question_data = active_questions[question_key]
    correct_answers = question_data["correct_answers"]
    message_id = question_data.get("message_id")
    start_time = question_data["start_time"]
    elapsed_time = time.time() - start_time
    question_type = question_data["type"]

    timeout_end = question_data.get(f"timeout_end_{user_id}", 0)
    current_time = time.time()
    if timeout_end > current_time:
        remaining_time = int(timeout_end - current_time)
        plural_suffix = "s" if remaining_time != 1 else ""
        await query.answer(
            localized["wrong_answer"].format(user_name=user_name) + "\n\n" +
            localized["timeout_remaining"].format(remaining_time=remaining_time, s=plural_suffix),
            show_alert=True
        )
        return

    if selected_answer in correct_answers:
        await process_correct_answer(update, chat_id, user_id, user_name, selected_answer, elapsed_time, question_type, message_id, context, question_key)
    else:
        global streak_data, achievements_data
        user_id_str = str(user_id)
        chat_id_str = str(chat_id)
        if chat_id_str not in streak_data:
            streak_data[chat_id_str] = {}
        if user_id_str not in streak_data[chat_id_str]:
            streak_data[chat_id_str][user_id_str] = {"name": user_name, "streak": 0}
        else:
            streak_data[chat_id_str][user_id_str]["streak"] = 0
        await save_streak_data(streak_data)
        logger.info(f"Streak reset to 0 for user {user_id} in chat {chat_id}")

        # Increment incorrect answers
        if user_id_str not in achievements_data:
            achievements_data[user_id_str] = {
                "correct_answers": 0,
                "current_streak": 0,
                "highest_streak": 0,
                "quick_answers": 0,
                "taylor_answers": 0,
                "lyrics_answers": 0,
                "incorrect_answers": 0,
                "groups_participated": 0,
                "total_points": 0,
                "achievements": []
            }
        achievements_data[user_id_str]["incorrect_answers"] += 1
        earned_achievements, achievements_data = update_achievements(user_id=user_id_str)
        await save_achievements_data(achievements_data)

        timeout_duration = 5
        timeout_end_time = current_time + timeout_duration
        question_data[f"timeout_end_{user_id}"] = timeout_end_time

        context.job_queue.run_once(
            reenable_buttons,
            timeout_duration,
            chat_id=chat_id,
            name=f"timeout_{question_key}",
            data={"message_id": message_id, "question_key": question_key, "selected_answer": selected_answer}
        )

        await query.answer(
            localized["wrong_answer"].format(user_name=user_name) + "\n\n" +
            localized["timeout_initial"].format(timeout_duration=timeout_duration),
            show_alert=True
        )

    await query.answer()

#RE-ENABLE BUTTONS
async def reenable_buttons(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    message_id = job.data["message_id"]
    question_key = job.data["question_key"]

    if question_key not in active_questions:
        logger.info(f"Question {question_key} no longer active, skipping button re-enabling")
        return

    question_data = active_questions[question_key]
    if question_data["answered"] and "selected_answer" in job.data and job.data["selected_answer"] not in question_data["correct_answers"]:
        # REBUILD THE ORIGINAL BUTTONS
        group_settings = load_group_settings()
        answer_mode = group_settings.get(str(chat_id), {}).get("answer_mode", "buttons")
        if answer_mode == "buttons":
            question_type = question_data["type"]
            question_data_raw = random.choice(lyrics_questions if question_type == "lyrics" else taylor_questions)
            options = question_data_raw["options"]
            random.shuffle(options)
            buttons = [[InlineKeyboardButton(f"›› {opt}", callback_data=f"answer_{opt.lower()}")] for opt in options]
            reply_markup = InlineKeyboardMarkup(buttons)

            try:
                await context.bot.edit_message_reply_markup(
                    chat_id=chat_id,
                    message_id=message_id,
                    reply_markup=reply_markup
                )
                logger.info(f"Re-enabled buttons for question {question_key} after timeout")
                active_questions[question_key]["answered"] = False
                if "timeout_end" in question_data:
                    del question_data["timeout_end"]
            except Exception as e:
                logger.error(f"Failed to re-enable buttons for question {question_key}: {e}")
                
# HANDLE TEXT-BASED ANSWERS
async def handle_text_answer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat_id
    user_id = update.message.from_user.id
    user_name = update.message.from_user.first_name
    raw_answer = update.message.text.strip().lower()
    selected_answer = sanitize_input(raw_answer)
    replied_to = update.message.reply_to_message
    
    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])
    answer_mode = group_settings.get(str(chat_id), {}).get("answer_mode", "buttons")
    
    if answer_mode != "write":
        return
    
    question_key = None
    recent_question = None
    for key, data in active_questions.items():
        if str(data["chat_id"]) == str(chat_id) and not data["answered"]:
            if recent_question is None or data["start_time"] > active_questions[recent_question]["start_time"]:
                recent_question = key
    
    if replied_to:
        question_key = f"{chat_id}_{replied_to.message_id}"
        if question_key not in active_questions:
            logger.info(f"No active question found for replied message {replied_to.message_id} in chat {chat_id}")
            return
    elif recent_question:
        question_key = recent_question
    else:
        logger.info(f"No active unanswered question found in chat {chat_id}")
        return
    
    logger.info(f"Processing text answer in chat {chat_id} with language {group_language} and answer mode {answer_mode}")
    logger.info(f"User answer: '{selected_answer}' | Correct answers: {active_questions[question_key]['correct_answers']} | Raw input: '{raw_answer}' | Question key: {question_key}")
    
    await save_user_emoji(user_id, user_name)

    question_data = active_questions[question_key]
    correct_answers = question_data["correct_answers"]
    message_id = question_data.get("message_id")
    start_time = question_data["start_time"]
    elapsed_time = time.time() - start_time
    question_type = question_data["type"]
    
    if selected_answer in correct_answers:
        logger.info(f"Correct answer detected for question {question_key} in chat {chat_id}")
        await process_correct_answer(update, chat_id, user_id, user_name, selected_answer, elapsed_time, question_type, update.message.message_id, context, question_key)
        
        random_emoji = random.choice(RANDOM_EMOJIS)
        try:
            await client(SendReactionRequest(
                peer=chat_id,
                big=True,
                msg_id=update.message.message_id,
                reaction=[ReactionEmoji(emoticon=random_emoji)],
            ))
            logger.info(f"Sent BIG emoji reaction {random_emoji} as bot in chat {chat_id}")
        except Exception as e:
            logger.error(f"Failed to send reaction: {e}")
        
        if elapsed_time < 300:
            alarm_jobs = context.job_queue.get_jobs_by_name(f"alarm_{question_key}")
            for job in alarm_jobs:
                job.schedule_removal()
                logger.info(f"Removed scheduled alarm job for question {question_key} after correct answer before halftime")
    else:
        global streak_data, achievements_data
        user_id_str = str(user_id)
        chat_id_str = str(chat_id)
        if chat_id_str not in streak_data:
            streak_data[chat_id_str] = {}
        if user_id_str not in streak_data[chat_id_str]:
            streak_data[chat_id_str][user_id_str] = {"name": user_name, "streak": 0}
        else:
            streak_data[chat_id_str][user_id_str]["streak"] = 0
        await save_streak_data(streak_data)
        logger.info(f"Streak reset to 0 for user {user_id} in chat {chat_id}")

        # Increment incorrect answers
        if user_id_str not in achievements_data:
            achievements_data[user_id_str] = {
                "correct_answers": 0,
                "current_streak": 0,
                "highest_streak": 0,
                "quick_answers": 0,
                "taylor_answers": 0,
                "lyrics_answers": 0,
                "incorrect_answers": 0,
                "groups_participated": 0,
                "total_points": 0,
                "achievements": []
            }
        achievements_data[user_id_str]["incorrect_answers"] += 1
        earned_achievements, achievements_data = update_achievements(user_id=user_id_str)
        await save_achievements_data(achievements_data)

#Process Correct Answer
async def process_correct_answer(update, chat_id, user_id, user_name, selected_answer, formatted_time, question_type, reply_message_id, context, question_key):
    elapsed_time_seconds = float(formatted_time)
    if elapsed_time_seconds <= 10:
        points = 10
    elif elapsed_time_seconds <= 60:
        points = 8
    elif elapsed_time_seconds <= 180:
        points = 6
    elif elapsed_time_seconds <= 300:
        points = 4
    elif elapsed_time_seconds <= 420:
        points = 2
    elif elapsed_time_seconds <= 600:
        points = 1
    else:
        points = 0

    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])
    logger.info(f"Using language {group_language} for chat {chat_id}")

    minutes = int(elapsed_time_seconds // 60)
    seconds = int(elapsed_time_seconds % 60)
    minute_key = "minutes" if minutes > 1 else "minute"
    second_key = "seconds" if seconds != 1 else "second"
    formatted_time = f"{minutes} {localized[minute_key]} {seconds} {localized[second_key]}!" if minutes > 0 else f"{seconds} {localized[second_key]}!"

    global leaderboard_data
    chat_id_str = str(chat_id)
    user_id_str = str(user_id)
    if chat_id_str not in leaderboard_data:
        leaderboard_data[chat_id_str] = {"players": {}}
    if user_id_str not in leaderboard_data[chat_id_str]["players"]:
        leaderboard_data[chat_id_str]["players"][user_id_str] = {"name": user_name, "score": 0}
    leaderboard_data[chat_id_str]["players"][user_id_str]["score"] += points
    logger.info(f"Updated leaderboard for chat {chat_id}, user {user_id}: {leaderboard_data[chat_id_str]}")
    await save_leaderboard(leaderboard_data)

    group_name = update.effective_chat.title
    await update_global_leaderboard(user_id, user_name, chat_id, group_name, points)

    # Streak handling (group-specific)
    global streak_data
    if chat_id_str not in streak_data:
        streak_data[chat_id_str] = {}
    if user_id_str not in streak_data[chat_id_str]:
        streak_data[chat_id_str][user_id_str] = {"name": user_name, "streak": 0}
    current_streak = streak_data[chat_id_str][user_id_str]["streak"]
    total_streak = current_streak + 1
    streak_data[chat_id_str][user_id_str]["streak"] = total_streak
    streak_data[chat_id_str][user_id_str]["name"] = user_name  # Update name if changed
    await save_streak_data(streak_data)
    streak = total_streak
    logger.info(f"Streak incremented to {streak} for user {user_id} in chat {chat_id}")

    global_rank = get_global_rank(user_id)
    earned_achievements, achievements_data = update_achievements(
        user_id=user_id,
        correct_answers=1,
        current_streak=streak,
        highest_streak=streak,
        quick_answer=elapsed_time_seconds <= 10,
        question_type=question_type,
        points=points,
        chat_id=chat_id
    )
    await save_achievements_data(achievements_data)

    response_text = localized["correct_lyrics"].format(user_id=user_id, user_name=user_name, formatted_time=formatted_time, points=points) if question_type == "lyrics" else localized["correct_taylor"].format(user_id=user_id, user_name=user_name, formatted_time=formatted_time, points=points)
    try:
        await context.bot.send_message(
            chat_id=chat_id,
            text=response_text,
            parse_mode=ParseMode.HTML,
            reply_to_message_id=reply_message_id
        )
        logger.info(f"Sent correct answer message for user {user_id} in chat {chat_id}")
    except Exception as e:
        logger.error(f"Failed to send correct answer message for user {user_id} in chat {chat_id}: {e}")

    question_message_id = active_questions[question_key].get("message_id")
    if question_message_id:
        try:
            caption = localized["answered_lyrics"] if question_type == "lyrics" else localized["answered_taylor"]
            await context.bot.edit_message_caption(
                chat_id=chat_id,
                message_id=question_message_id,
                caption=caption,
                parse_mode=ParseMode.HTML,
                reply_markup=None
            )
            logger.info(f"Question caption updated to 'Answered' for question {question_key}")
        except Exception as e:
            logger.error(f"Failed to edit question caption for question {question_key}: {e}")

    active_questions[question_key]["answered"] = True
    alarm_jobs = context.job_queue.get_jobs_by_name(f"alarm_{question_key}")
    for job in alarm_jobs:
        job.schedule_removal()
        logger.info(f"Removed scheduled alarm job for question {question_key} in process_correct_answer")

    if "alarm_message_id" in active_questions[question_key]:
        alarm_message_id = active_questions[question_key]["alarm_message_id"]
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=alarm_message_id)
            logger.info(f"Alarm message {alarm_message_id} deleted for question {question_key}")
            del active_questions[question_key]["alarm_message_id"]
        except Exception as e:
            logger.error(f"Failed to delete alarm message {alarm_message_id} for question {question_key}: {e}")

    if question_key in active_questions:
        del active_questions[question_key]
        logger.info(f"Question {question_key} removed from active_questions after correct answer")
        
# Delete wrong answer message
async def delete_wrong_answer(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    message_id = job.data["message_id"]

    try:
        await context.bot.delete_message(chat_id, message_id)
    except:
        pass

# Save leaderboard data
async def save_leaderboard(data):
    with get_db_connection() as conn:
        cursor = conn.cursor()
        for chat_id in data:
            cursor.execute("DELETE FROM leaderboard WHERE chat_id = ?", (chat_id,))
            for user_id, user_data in data[chat_id]["players"].items():
                cursor.execute("""
                    INSERT OR REPLACE INTO leaderboard (chat_id, user_id, name, score)
                    VALUES (?, ?, ?, ?)
                """, (chat_id, user_id, user_data["name"], user_data["score"]))
        conn.commit()
        logger.info("Leaderboard data saved to SQLite.")
    return True


# Save global leaderboard data
async def save_global_leaderboard(data):
    with get_db_connection() as conn:
        cursor = conn.cursor()
        cursor.execute("DELETE FROM global_leaderboard")
        cursor.execute("DELETE FROM global_leaderboard_groups")
        for user_id, user_data in data.items():
            cursor.execute("""
                INSERT OR REPLACE INTO global_leaderboard (user_id, name, score)
                VALUES (?, ?, ?)
            """, (user_id, user_data["name"], user_data["score"]))
            for group_id, group_data in user_data["groups"].items():
                cursor.execute("""
                    INSERT OR REPLACE INTO global_leaderboard_groups (user_id, group_id, group_name, score)
                    VALUES (?, ?, ?, ?)
                """, (user_id, group_id, group_data["group_name"], group_data["score"]))
        conn.commit()
        logger.info("Global leaderboard saved to SQLite.")
        return True


# Update global leaderboard when a player scores points
async def update_global_leaderboard(user_id, user_name, chat_id, group_name, points):
    global global_leaderboard, achievements_data
    user_id_str = str(user_id)
    chat_id_str = str(chat_id)

    logger.debug(f"Accessing achievements_data: {achievements_data}")
    async with ACHIEVEMENTS_DATA_LOCK:
        # Initialize achievements_data if None or empty
        if achievements_data is None:
            logger.warning("achievements_data is None, initializing as empty dict")
            achievements_data = {}

        # Update global leaderboard
        if user_id_str not in global_leaderboard:
            global_leaderboard[user_id_str] = {"name": user_name, "score": 0, "groups": {}}
        global_leaderboard[user_id_str]["score"] += points
        global_leaderboard[user_id_str]["groups"][chat_id_str] = {
            "group_name": group_name,
            "score": global_leaderboard[user_id_str]["groups"].get(chat_id_str, {"score": 0})["score"] + points
        }

        # Update achievements data
        if user_id_str in achievements_data:
            achievements_data[user_id_str]["total_points"] += points
            achievements_data[user_id_str]["groups_participated"] = len(global_leaderboard[user_id_str]["groups"])
        else:
            achievements_data[user_id_str] = {
                "correct_answers": 0,
                "current_streak": 0,
                "highest_streak": 0,
                "quick_answers": 0,
                "taylor_answers": 0,
                "lyrics_answers": 0,
                "incorrect_answers": 0,
                "groups_participated": 1,
                "total_points": points,
                "achievements": []
            }

    # Save data outside the lock to reduce contention
    await save_global_leaderboard(global_leaderboard)
    await save_achievements_data(achievements_data)

# Get top 50 players from the global leaderboard
def get_top_players(limit=50):
    global_leaderboard = load_global_leaderboard()
    sorted_players = sorted(
        global_leaderboard.items(),
        key=lambda x: x[1]["score"],
        reverse=True
    )[:limit]  # Use limit instead of hardcoded 50
    return sorted_players

#FUNCTION TO GET THE TOP 10 PLAYERS BY LANGUAGE
def get_top_players_by_language(language):
    global_leaderboard = load_global_leaderboard()
    user_languages = load_user_languages()
    
    # Filter players by language
    players_by_lang = {
        user_id: data for user_id, data in global_leaderboard.items()
        if user_languages.get(user_id, "en") == language and data["score"] > 0
    }
    
    # Sort and limit to top 10
    sorted_players = sorted(
        players_by_lang.items(),
        key=lambda x: x[1]["score"],
        reverse=True
    )[:10]  # Limit to top 10
    return sorted_players


# Get top 10 groups from the global leaderboard
def get_top_groups():
    global_leaderboard = load_global_leaderboard()
    group_scores = {}
    
    for user_id, user_data in global_leaderboard.items():
        # Check if "groups" exists (new structure)
        if "groups" in user_data:
            for group_id, group_data in user_data["groups"].items():
                if group_id not in group_scores:
                    group_scores[group_id] = {
                        "name": group_data["group_name"],
                        "score": 0
                    }
                group_scores[group_id]["score"] += group_data["score"]
        # Handle old structure for backward compatibility (optional)
        elif "group_id" in user_data:
            group_id = str(user_data["group_id"])
            if group_id not in group_scores:
                group_scores[group_id] = {
                    "name": user_data.get("group_name", "Unknown Group"),
                    "score": 0
                }
            group_scores[group_id]["score"] += user_data["score"]

    sorted_groups = sorted(
        group_scores.items(),
        key=lambda x: x[1]["score"],
        reverse=True
    )[:MAX_PLAYERS]
    return sorted_groups

# Normalize username for leaderboard
def remove_emojis(text):
    if not text:  # Ensure the input is not None or empty
        return ""
    emoji_pattern = re.compile("["
        u"\U0001F600-\U0001F64F"  # Emoticons
        u"\U0001F300-\U0001F5FF"  # Symbols & pictographs
        u"\U0001F680-\U0001F6FF"  # Transport & map symbols
        u"\U0001F700-\U0001F77F"  # Alchemical symbols
        u"\U0001F780-\U0001F7FF"  # Geometric symbols
        u"\U0001F800-\U0001F8FF"  # Supplemental arrows
        u"\U0001F900-\U0001F9FF"  # Supplemental symbols & pictographs
        u"\U0001FA00-\U0001FA6F"  # Chess symbols, objects, hands
        u"\U0001FA70-\U0001FAFF"  # More symbols
        u"\U00002702-\U000027B0"  # Dingbats
        u"\U000024C2-\U0001F251"
        "]+", flags=re.UNICODE)
    return emoji_pattern.sub(r'', text)


def normalize_username(name):
    if not name:
        return ""

    # Normalize Unicode characters
    normalized = unicodedata.normalize("NFKC", name)

    # Remove emojis and special characters
    sanitized = re.sub(r"[^\w\s]", "", normalized)
    sanitized = re.sub(r"\d+", "", sanitized)  # Remove numbers

    # Convert to title case and remove extra spaces
    formatted = sanitized.lower().title().strip()

    return formatted

#Implementation of get_user_profile_photo
async def get_user_profile_photo(user_id):
    try:
        # Fetch the user's profile photos
        photos = await application.bot.get_user_profile_photos(user_id, limit=1)

        if photos.total_count > 0:
            # Get the largest available photo
            photo = photos.photos[0][-1]
            file_id = photo.file_id

            # Download the photo
            file = await application.bot.get_file(file_id)
            file_path = f"temp_profile_photo_{user_id}.jpg"
            await file.download_to_drive(file_path)

            return file_path
        else:
            # No profile photo available
            return None
    except Exception as e:
        logger.error(f"Error fetching profile photo for user {user_id}: {e}")
        return None

# Detect language of the text leaderboard
def detect_language(text):
    if not text:
        return "en"

    # Check for Japanese characters
    if re.search(r'[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]', text):
        return "ja"

    # Check for Korean characters
    if re.search(r'[\uAC00-\uD7AF]', text):
        return "ko"

    # Check for Arabic characters
    if re.search(r'[\u0600-\u06FF]', text):
        return "ar"

    # Default to English
    return "en"

# Detect language of the text profile
def detect_language1(text):
    if not text:
        return "eng"

    # Check for Japanese characters
    if re.search(r'[\u3040-\u309F\u30A0-\u30FF\u4E00-\u9FAF]', text):
        return "jap"

    # Check for Korean characters
    if re.search(r'[\uAC00-\uD7AF]', text):
        return "kor"

    # Check for Arabic characters
    if re.search(r'[\u0600-\u06FF]', text):
        return "ara"

    # Default to English
    return "eng"


# Truncate text with '...' if it exceeds max_width
def truncate_text(draw, text, max_width, font):
    # Check if the text width exceeds the max_width
    text_width = draw.textbbox((0, 0), text, font=font)[2]

    if text_width > max_width:
        while draw.textbbox((0, 0), text, font=font)[2] > max_width and len(text) > 3:
            text = text[:-1]  # Remove one character at a time
        return text + "  "  # Add ellipsis to indicate truncation
    else:
        return text  # Return the original text if it fits within the max_width
    
    
#achivements
def update_achievements(user_id, correct_answers=0, current_streak=0, highest_streak=0, quick_answer=False, question_type=None, points=0, chat_id=None):
    global achievements_data
    user_id = str(user_id)
    earned_achievements = []

    # Initialize user data if not present
    if user_id not in achievements_data:
        achievements_data[user_id] = {
            "correct_answers": 0,
            "current_streak": 0,
            "highest_streak": 0,
            "quick_answers": 0,
            "taylor_answers": 0,
            "lyrics_answers": 0,
            "incorrect_answers": 0,
            "groups_participated": 0,
            "total_points": 0,
            "achievements": []
        }
    
    user_data = achievements_data[user_id]

    # Update stats
    user_data["correct_answers"] += correct_answers
    user_data["current_streak"] = current_streak
    if current_streak > user_data["highest_streak"]:
        user_data["highest_streak"] = current_streak
    if quick_answer:
        user_data["quick_answers"] += 1
    if question_type == "taylor":
        user_data["taylor_answers"] += 1
    elif question_type == "lyrics":
        user_data["lyrics_answers"] += 1
    user_data["total_points"] += points

    # Update groups participated
    if chat_id and str(chat_id) not in global_leaderboard.get(user_id, {}).get("groups", {}):
        user_data["groups_participated"] += 1

    # Check for new achievements
    for ach_id, ach_data in ACHIEVEMENTS.items():
        if ach_id in user_data["achievements"]:
            continue  # Skip already earned achievements
        threshold = ach_data["threshold"]
        achieved = False

        if ach_id in ["fearless_beginner", "love_story_enthusiast", "red_hot_player", "1989_master", "reputation_legend", "22_enthusiast"]:
            achieved = user_data["correct_answers"] >= threshold
        elif ach_id == "lover_of_lyrics":
            achieved = user_data["lyrics_answers"] >= threshold
        elif ach_id == "swift_pro":
            achieved = user_data["taylor_answers"] >= threshold
        elif ach_id in ["speak_now_streak", "evermore_streak", "delicate_streak", "long_live_legend"]:
            achieved = user_data["highest_streak"] >= threshold
        elif ach_id == "shake_it_off_quick":
            achieved = user_data["quick_answers"] >= threshold
        elif ach_id == "style_icon":
            achieved = user_data["groups_participated"] >= threshold
        elif ach_id == "cardigan_collector":
            achieved = user_data["total_points"] >= threshold
        elif ach_id == "willow_wizard":
            achieved = user_data["correct_answers"] >= threshold and user_data["quick_answers"] >= threshold
        elif ach_id == "bad_blood_buster":
            achieved = user_data["incorrect_answers"] >= threshold
        elif ach_id == "swiftie_supreme":
            # Check if all other achievements are earned
            other_achievements = set(ACHIEVEMENTS.keys()) - {"swiftie_supreme"}
            achieved = all(ach in user_data["achievements"] for ach in other_achievements)

        if achieved:
            user_data["achievements"].append(ach_id)
            earned_achievements.append(ach_id)
            logger.info(f"User {user_id} earned achievement: {ach_id}")

    return earned_achievements, achievements_data

#profile picture
def generate_profile_image(user_name, profile_photo_path, text_x=40, text_y=10, logo_path="logo.png", logo_x=890, logo_y=890):
    try:
        # Load the profile picture
        if profile_photo_path:
            img = Image.open(profile_photo_path).convert("RGBA")  # Ensure the image has an alpha channel
        else:
            # Use a default image if no profile picture is available
            img = Image.new("RGBA", (500, 500), color=(128, 128, 128, 255))  # Default gray background

        # Resize the image to a standard size (optional)
        img = img.resize((1000, 1000))

        # Load the transparent logo
        logo = Image.open(logo_path).convert("RGBA")  # Ensure the logo has an alpha channel
        logo = logo.resize((100, 100))  # Resize the logo to fit

        # Overlay the logo on the profile picture
        img.paste(logo, (logo_x, logo_y), logo)  # Use the logo's alpha channel for transparency

        # Initialize ImageDraw
        draw = ImageDraw.Draw(img)

        # Detect language of the user's name
        language = detect_language1(user_name)

        # Load appropriate font based on language
        font_path = FONT_PATHS2.get(language, FONT_PATHS2["eng"])  # Default to English if language not found
        font = ImageFont.truetype(font_path, 60)

        # Normalize the user's name
        normalized_name = normalize_username(user_name)

        # Convert name to CAPS (without numbers)
        user_name_caps = normalized_name.upper()

        # Add user name to the image at the specified position
        draw.text((text_x, text_y), user_name_caps, fill="white", font=font)

        # Save the generated image to memory
        image_io = io.BytesIO()
        img.save(image_io, format="PNG")  # Use PNG to preserve transparency
        image_io.seek(0)

        return image_io

    except Exception as e:
        logger.error(f"Error generating profile image: {e}")
        return None
    
#Profile Command  
async def profile(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = str(update.message.from_user.id)  # Ensure string for consistency
    chat = update.message.chat
    chat_id = str(chat.id)  # Ensure string for consistency

    # Ensure this only works in group chats
    if chat.type == "private":
        return

    # Check if bot can operate
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        return

    # Load group settings and get language
    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Check rate limit
    if is_rate_limited(user_id, "profile"):
        warning_message = await update.message.reply_text(localized["rate_limit"])
        context.job_queue.run_once(
            delete_message,
            when=5,
            chat_id=chat_id,
            data={"message_id": warning_message.message_id}
        )
        return

    # Fetch user data
    user = update.message.from_user

    # Fetch user's profile photo (assuming this function exists)
    profile_photo_path = await get_user_profile_photo(user_id)

    # Load data
    leaderboard_data = load_leaderboard()
    streak_data = load_streak_data()
    achievements_data = load_achievements_data()
    global_leaderboard = load_global_leaderboard()

    # Get user's score and streak
    user_score = leaderboard_data.get(chat_id, {}).get("players", {}).get(user_id, {}).get("score", 0)
    user_streak = streak_data.get(chat_id, {}).get(user_id, {}).get("streak", 0)

    # Get user's total points from the global leaderboard
    total_points = global_leaderboard.get(user_id, {}).get("score", 0)

    # Get user's local rank
    sorted_local_players = sorted(
        leaderboard_data.get(chat_id, {}).get("players", {}).items(),
        key=lambda x: x[1]["score"], reverse=True
    )
    local_rank = next((i + 1 for i, (uid, _) in enumerate(sorted_local_players) if uid == user_id), None)

    # Get user's global rank
    global_rank = get_global_rank(user_id)

    # Get user's achievements (include both unnotified and notified)
    user_achievements_data = achievements_data.get(user_id, {})
    user_achievements = user_achievements_data.get("achievements", []) + user_achievements_data.get("notified_achievements", [])

    # Get user's emoji from USER_EMOJIS (backed by user_emojis table)
    user_emoji = get_emoji_for_user(user_id)

    # Generate profile image (assuming this function exists)
    profile_image = generate_profile_image(user.first_name, profile_photo_path)

    # Prepare profile message using localized strings
    profile_message = (
        f"{user_emoji} <b>{user.first_name}</b>\n\n"
        f"🏆 <b>{localized['score']}</b> {user_score} {localized['points_local']}\n"
        f"🌟 <b>{localized['total_points']}</b> {total_points} {localized['points_global']}\n"
        f"🔥 <b>{localized['streak']}</b> {user_streak}\n"
        f"🏅 <b>{localized['local_rank']}</b> #{local_rank if local_rank else localized['na']}\n"
        f"🌍 <b>{localized['global_rank']}</b> #{global_rank if global_rank else localized['na']}\n"
    )

    # Add achievements section
    if user_achievements:
        profile_message += f"\n{localized['achievements_title']}"
        for achievement_id in user_achievements:
            achievement = ACHIEVEMENTS.get(achievement_id)
            if achievement:
                profile_message += localized["achievement_entry"].format(achievement_name=achievement["name"])
            else:
                logger.warning(f"Achievement ID {achievement_id} not found in ACHIEVEMENTS for user {user_id}")
    else:
        profile_message += f"\n{localized['no_achievements']}"

    # Send the profile image and message
    await context.bot.send_photo(
        chat_id=chat_id,
        photo=profile_image,
        caption=profile_message,
        parse_mode=ParseMode.HTML
    )

    # Clean up the temporary profile photo file
    if profile_photo_path and os.path.exists(profile_photo_path):
        os.remove(profile_photo_path)

# Generate leaderboard image dynamically
async def generate_leaderboard_image(chat_id):
    async with IMAGE_GEN_SEMAPHORE:  # Limit concurrent generations
        group_settings = load_group_settings()
        group_language = group_settings.get(str(chat_id), {}).get("language", "en")
        logger.info(f"Generating leaderboard for chat {chat_id} with language {group_language}")

        leaderboard_data = load_leaderboard()
        if str(chat_id) not in leaderboard_data or "players" not in leaderboard_data[str(chat_id)]:
            return None

        players = leaderboard_data[str(chat_id)]["players"]
        data_hash = hashlib.sha256(str(players).encode()).hexdigest()  # Hash for caching

        # Check cache first
        cache_key = f"{chat_id}_{data_hash}"
        if cache_key in LEADERBOARD_IMAGE_CACHE:
            cached_image = LEADERBOARD_IMAGE_CACHE[cache_key]
            if cached_image and cached_image.tell() > 0:
                cached_image.seek(0)  # Rewind to the start for reuse
                logger.info(f"Returning cached leaderboard image for chat {chat_id}")
                return cached_image

        sorted_players = sorted(players.items(), key=lambda x: x[1]["score"], reverse=True)[:MAX_PLAYERS]
        if not sorted_players:
            return None

        img = BASE_TEMPLATES.get(group_language, BASE_TEMPLATES["en"]).copy()  # Use preloaded template
        draw = ImageDraw.Draw(img)

        font_size = 120
        score_font_size = 100
        name_start_x = 500
        name_start_y = 850
        rounded_rect_start_x = 1400
        rounded_rect_start_y = 850
        rounded_rect_width_max = 4000
        rounded_rect_height = 185
        rounded_rect_fill = "white"
        rounded_rect_outline = "white"
        rounded_rect_radius = 120
        normal_rect_start_x = 1400
        normal_rect_start_y = 850
        normal_rect_width = 100
        normal_rect_height = 185
        normal_rect_fill = "white"
        normal_rect_outline = "white"
        spacing = 230
        max_score = max([p["score"] for p in players.values()])
        max_name_width = rounded_rect_start_x - name_start_x - 50

        for index, (user_id, data) in enumerate(sorted_players):
            # Convert name to uppercase and remove numbers
            name = normalize_username(data['name']).upper()  # Already removes numbers, now in caps
            language = detect_language(name)
            font_path = FONT_PATHS.get(language, FONT_PATHS["en"])
            font = ImageFont.truetype(font_path, font_size)

            truncated_name = truncate_text(draw, name, max_name_width, font)
            draw.text((name_start_x, name_start_y + index * spacing), truncated_name, fill="white", font=font)

            score = data["score"]
            rounded_rect_length = (score / max_score) * rounded_rect_width_max if max_score > 0 else 0
            draw.rounded_rectangle(
                (rounded_rect_start_x, rounded_rect_start_y + index * spacing,
                 rounded_rect_start_x + rounded_rect_length,
                 rounded_rect_start_y + index * spacing + rounded_rect_height),
                fill=rounded_rect_fill, outline=rounded_rect_outline, radius=rounded_rect_radius
            )
            draw.rectangle(
                (normal_rect_start_x, normal_rect_start_y + index * spacing,
                 normal_rect_start_x + normal_rect_width,
                 normal_rect_start_y + index * spacing + normal_rect_height),
                fill=normal_rect_fill, outline=normal_rect_outline
            )

            score_text = str(score)
            bbox = draw.textbbox((0, 0), score_text, font=ImageFont.truetype(FONT_PATHS["en"], score_font_size))
            text_width = bbox[2] - bbox[0]
            text_height = bbox[3] - bbox[1]
            text_x = rounded_rect_start_x + (rounded_rect_length - text_width) / 2
            text_y = rounded_rect_start_y + index * spacing + (rounded_rect_height - text_height) / 2 - 30
            draw.text((text_x, text_y), score_text, fill="#1B1A36", font=ImageFont.truetype(FONT_PATHS["en"], score_font_size))

        image_io = io.BytesIO()
        img.save(image_io, format="JPEG")
        image_io.seek(0)

        # Store in cache
        LEADERBOARD_IMAGE_CACHE[cache_key] = image_io
        logger.info(f"Generated and cached leaderboard image for chat {chat_id}")
        return image_io

# Generate streak leaderboard image dynamically
async def generate_streak_leaderboard_image(chat_id):
    async with IMAGE_GEN_SEMAPHORE:
        group_settings = load_group_settings()
        group_language = group_settings.get(str(chat_id), {}).get("language", "en")
        logger.info(f"Generating streak leaderboard for chat {chat_id} with language {group_language}")

        streak_data = load_streak_data()
        if str(chat_id) not in streak_data:
            return None

        players = streak_data[str(chat_id)]
        data_hash = hashlib.sha256(str(players).encode()).hexdigest()

        # Check cache first
        cache_key = f"{chat_id}_{data_hash}"
        if cache_key in STREAK_IMAGE_CACHE:
            cached_image = STREAK_IMAGE_CACHE[cache_key]
            if cached_image and cached_image.tell() > 0:
                cached_image.seek(0)  # Rewind to the start for reuse
                logger.info(f"Returning cached streak image for chat {chat_id}")
                return cached_image

        sorted_players = sorted(
            [(user_id, data) for user_id, data in players.items() if data["streak"] > 0],
            key=lambda x: x[1]["streak"], reverse=True
        )[:MAX_PLAYERS]
        if not sorted_players:
            return None

        img = BASE_STREAK_TEMPLATES.get(group_language, BASE_STREAK_TEMPLATES["en"]).copy()
        draw = ImageDraw.Draw(img)

        font_size = 120
        streak_font_size = 100
        name_start_x = 500
        name_start_y = 850
        rounded_rect_start_x = 1400
        rounded_rect_start_y = 850
        rounded_rect_width_max = 4000
        rounded_rect_height = 185
        rounded_rect_fill = "white"
        rounded_rect_outline = "white"
        rounded_rect_radius = 120
        normal_rect_start_x = 1400
        normal_rect_start_y = 850
        normal_rect_width = 100
        normal_rect_height = 185
        normal_rect_fill = "white"
        normal_rect_outline = "white"
        spacing = 230
        max_streak = max([p["streak"] for p in players.values() if p["streak"] > 0], default=1)
        max_name_width = rounded_rect_start_x - name_start_x - 50

        for index, (user_id, data) in enumerate(sorted_players):
            # Convert name to uppercase and remove numbers
            name = normalize_username(data['name']).upper()  # Already removes numbers, now in caps
            language = detect_language(name)
            font_path = FONT_PATHS.get(language, FONT_PATHS["en"])
            font = ImageFont.truetype(font_path, font_size)

            truncated_name = truncate_text(draw, name, max_name_width, font)
            draw.text((name_start_x, name_start_y + index * spacing), truncated_name, fill="white", font=font)

            streak = data["streak"]
            rounded_rect_length = (streak / max_streak) * rounded_rect_width_max if max_streak > 0 else 0
            draw.rounded_rectangle(
                (rounded_rect_start_x, rounded_rect_start_y + index * spacing,
                 rounded_rect_start_x + rounded_rect_length,
                 rounded_rect_start_y + index * spacing + rounded_rect_height),
                fill=rounded_rect_fill, outline=rounded_rect_outline, radius=rounded_rect_radius
            )
            draw.rectangle(
                (normal_rect_start_x, normal_rect_start_y + index * spacing,
                 normal_rect_start_x + normal_rect_width,
                 normal_rect_start_y + index * spacing + normal_rect_height),
                fill=normal_rect_fill, outline=normal_rect_outline
            )

            streak_text = str(streak)
            bbox = draw.textbbox((0, 0), streak_text, font=ImageFont.truetype(FONT_PATHS["en"], streak_font_size))
            text_width = bbox[2] - bbox[0]
            text_height = bbox[3] - bbox[1]
            text_x = rounded_rect_start_x + (rounded_rect_length - text_width) / 2
            text_y = rounded_rect_start_y + index * spacing + (rounded_rect_height - text_height) / 2 - 30
            draw.text((text_x, text_y), streak_text, fill="#1B1A36", font=ImageFont.truetype(FONT_PATHS["en"], streak_font_size))

        image_io = io.BytesIO()
        img.save(image_io, format="JPEG")
        image_io.seek(0)

        # Store in cache
        STREAK_IMAGE_CACHE[cache_key] = image_io
        logger.info(f"Generated and cached streak image for chat {chat_id}")
        return image_io


# Get top 10 global streaks
def get_top_global_streaks(language=None, limit=10):
    """Get top global streaks, optionally filtered by language."""
    global streak_data, user_languages
    player_totals = {}
    for chat_id, players in streak_data.items():
        if chat_id == "global":  # Skip if any leftover global section exists
            continue
        for user_id, data in players.items():
            # Apply language filter if specified
            if language and user_languages.get(user_id) != language:
                continue
            if user_id not in player_totals:
                player_totals[user_id] = {"name": data["name"], "streak": 0}
            player_totals[user_id]["streak"] += data["streak"]
            player_totals[user_id]["name"] = data["name"]

    # Filter players with positive streaks and sort
    player_streaks = [
        {"user_id": user_id, "name": data["name"], "streak": data["streak"]}
        for user_id, data in player_totals.items()
        if data["streak"] > 0
    ]
    sorted_streaks = sorted(player_streaks, key=lambda x: x["streak"], reverse=True)[:limit]
    return sorted_streaks


# Command to display streak options
async def streak_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.message.from_user.id
    chat = update.message.chat
    chat_id = str(chat.id)

    # Ensure this only works in group chats
    if chat.type == "private":
        return

    # Check if bot can operate
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        return

    # Check rate limit
    if is_rate_limited(user_id, "streak"):
        # Load group settings to get language
        group_settings = load_group_settings()
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        
        warning_message = await update.message.reply_text(localized["rate_limit"])
        context.job_queue.run_once(
            delete_message,
            when=5,
            chat_id=chat.id,
            data={"message_id": warning_message.message_id}
        )
        return

    # Load group settings and get language
    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Buttons for streak options
    keyboard = [
        [InlineKeyboardButton(localized["group_button"], callback_data="streak_local"),
         InlineKeyboardButton(localized["global_button"], callback_data="streak_global")],
        [InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    await update.message.reply_text(
        localized["options"],
        parse_mode=ParseMode.HTML,
        reply_markup=reply_markup
    )

# Callback handler for streak buttons
async def streak_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()
    data = query.data
    chat_id = query.message.chat_id
    user_id = query.from_user.id

    # Load group settings and localization
    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    if data == "streak_local":
        if is_rate_limited(user_id, "streak_local"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        streak_image = await generate_streak_leaderboard_image(chat_id)
        if streak_image:
            sorted_streaks = streak_data.get(str(chat_id), {})
            sorted_streaks = sorted(sorted_streaks.items(), key=lambda x: x[1]["streak"], reverse=True)[:10]
            caption = localized["local_title"]
            for index, (player_id, data) in enumerate(sorted_streaks, start=1):
                emoji = get_emoji_for_user(player_id)
                caption += localized["streak_entry"].format(
                    index=index, emoji=emoji, user_id=player_id, user_name=data["name"], streak=data["streak"]
                )
            if len(caption) > 4096:  # Explicitly check Telegram's limit
                caption = caption[:4090] + "..."
            try:
                await context.bot.send_photo(
                    chat_id=chat_id, photo=streak_image, caption=caption, parse_mode=ParseMode.HTML,
                    protect_content=True, has_spoiler=True, read_timeout=30, write_timeout=30, connect_timeout=30
                )
                await query.message.delete()
            except TimedOut:
                await query.message.edit_text(localized["timeout_error"], parse_mode=ParseMode.HTML)
            except Exception as e:
                logger.error(f"Error sending streak image: {e}")
                await query.message.edit_text(localized["generic_error"], parse_mode=ParseMode.HTML)
        else:
            keyboard = [[InlineKeyboardButton(localized["back_button"], callback_data="streak_back")]]
            await query.message.edit_text(
                localized["no_local_data"], parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
            )

    elif data == "streak_global":
        if is_rate_limited(user_id, "streak_global"):  # Added rate limiting
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        try:
            global_streaks = get_top_global_streaks()
            caption = localized["global_title"]
            if global_streaks:
                for index, data in enumerate(global_streaks, start=1):
                    emoji = get_emoji_for_user(data["user_id"])
                    caption += localized["streak_entry"].format(
                        index=index, emoji=emoji, user_id=data["user_id"], user_name=data["name"], streak=data["streak"]
                    )
            else:
                caption = localized["no_global_data"]
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            keyboard = [
                [InlineKeyboardButton(localized["language"], callback_data="streak_show_languages")],
                [InlineKeyboardButton(localized["back_button"], callback_data="streak_back"),
                 InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]
            ]
            await query.message.edit_text(
                caption, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
            )
        except Exception as e:
            logger.error(f"Error fetching global streaks: {e}")
            await query.message.edit_text(localized["generic_error"], parse_mode=ParseMode.HTML)

    elif data == "streak_show_languages":
        if is_rate_limited(user_id, "streak_show_languages"):  # Added rate limiting
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        try:
            global_streaks = get_top_global_streaks()
            caption = localized["global_title"]
            if global_streaks:
                for index, data in enumerate(global_streaks, start=1):
                    emoji = get_emoji_for_user(data["user_id"])
                    caption += localized["streak_entry"].format(
                        index=index, emoji=emoji, user_id=data["user_id"], user_name=data["name"], streak=data["streak"]
                    )
            else:
                caption = localized["no_global_data"]
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            # Simplified keyboard layout for clarity
            flag_buttons = [
                [InlineKeyboardButton(localized["global_button1"], callback_data="lang_streak_overall")],
                [InlineKeyboardButton("🇺🇸 EN", callback_data="lang_streak_en"),
                 InlineKeyboardButton("🇪🇸 ES", callback_data="lang_streak_es"),
                 InlineKeyboardButton("🇸🇦 AR", callback_data="lang_streak_ar")],
                [InlineKeyboardButton("🇮🇷 FA", callback_data="lang_streak_fa"),
                 InlineKeyboardButton("🇩🇪 DE", callback_data="lang_streak_de"),
                 InlineKeyboardButton("🇫🇷 FR", callback_data="lang_streak_fr")],
                [InlineKeyboardButton("🇮🇹 IT", callback_data="lang_streak_it"),
                 InlineKeyboardButton("🇵🇹 PT", callback_data="lang_streak_pt"),
                 InlineKeyboardButton("🇮🇩 ID", callback_data="lang_streak_id")],
                [InlineKeyboardButton("🇰🇷 KR", callback_data="lang_streak_ko"),
                 InlineKeyboardButton("🇷🇺 RU", callback_data="lang_streak_ru"),
                 InlineKeyboardButton("🇹🇷 TR", callback_data="lang_streak_tr")],
            ]
            keyboard = flag_buttons + [[InlineKeyboardButton(localized["back_button"], callback_data="streak_back"),
                                        InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]]
            await query.message.edit_text(
                caption, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
            )
        except Exception as e:
            logger.error(f"Error showing language streaks: {e}")
            await query.message.edit_text(localized["generic_error"], parse_mode=ParseMode.HTML)

    elif data.startswith("lang_streak_"):
        if is_rate_limited(user_id, data):  # Added rate limiting for language-specific options
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        try:
            selected_lang = data.split("_")[2]
            if selected_lang == "overall":
                global_streaks = get_top_global_streaks()
                caption = localized["global_title"]
            else:
                global_streaks = get_top_global_streaks(language=selected_lang)
                flag = LANGUAGE_FLAGS.get(selected_lang, "🏳️")
                caption = localized["top_players_lang_title"].format(flag=flag)  # Use consistent title
            if global_streaks:
                for index, data in enumerate(global_streaks, start=1):
                    emoji = get_emoji_for_user(data["user_id"])
                    caption += localized["streak_entry"].format(
                        index=index, emoji=emoji, user_id=data["user_id"], user_name=data["name"], streak=data["streak"]
                    )
            else:
                caption = localized["no_top_players_lang"].format(lang=selected_lang.upper()) if selected_lang != "overall" else localized["no_global_data"]
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            # Simplified keyboard with selected language highlighted
            flag_buttons = [
                InlineKeyboardButton(f"{localized['global_button1']} {'🔘' if selected_lang == 'overall' else ''}", callback_data="lang_streak_overall"),
                InlineKeyboardButton(f"🇺🇸 EN {'🔘' if selected_lang == 'en' else ''}", callback_data="lang_streak_en"),
                InlineKeyboardButton(f"🇪🇸 ES {'🔘' if selected_lang == 'es' else ''}", callback_data="lang_streak_es"),
                InlineKeyboardButton(f"🇸🇦 AR {'🔘' if selected_lang == 'ar' else ''}", callback_data="lang_streak_ar"),
                InlineKeyboardButton(f"🇮🇷 FA {'🔘' if selected_lang == 'fa' else ''}", callback_data="lang_streak_fa"),
                InlineKeyboardButton(f"🇩🇪 DE {'🔘' if selected_lang == 'de' else ''}", callback_data="lang_streak_de"),
                InlineKeyboardButton(f"🇫🇷 FR {'🔘' if selected_lang == 'fr' else ''}", callback_data="lang_streak_fr"),
                InlineKeyboardButton(f"🇮🇹 IT {'🔘' if selected_lang == 'it' else ''}", callback_data="lang_streak_it"),
                InlineKeyboardButton(f"🇵🇹 PT {'🔘' if selected_lang == 'pt' else ''}", callback_data="lang_streak_pt"),
                InlineKeyboardButton(f"🇮🇩 ID {'🔘' if selected_lang == 'id' else ''}", callback_data="lang_streak_id"),
                InlineKeyboardButton(f"🇰🇷 KR {'🔘' if selected_lang == 'ko' else ''}", callback_data="lang_streak_ko"),
                InlineKeyboardButton(f"🇷🇺 RU {'🔘' if selected_lang == 'ru' else ''}", callback_data="lang_streak_ru"),
                InlineKeyboardButton(f"🇹🇷 TR {'🔘' if selected_lang == 'tr' else ''}", callback_data="lang_streak_tr"),
            ]
            keyboard = [
                [flag_buttons[0]],
                flag_buttons[1:4],
                flag_buttons[4:7],
                flag_buttons[7:10],
                flag_buttons[10:13],
                [InlineKeyboardButton(localized["back_button"], callback_data="streak_back"),
                 InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]  # Added close button
            ]
            await query.message.edit_text(
                caption, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
            )
        except Exception as e:
            logger.error(f"Error handling language streak {selected_lang}: {e}")
            await query.message.edit_text(localized["generic_error"], parse_mode=ParseMode.HTML)

    elif data == "streak_back":
        keyboard = [
            [InlineKeyboardButton(localized["group_button"], callback_data="streak_local"),
             InlineKeyboardButton(localized["global_button"], callback_data="streak_global")],
            [InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]
        ]
        await query.message.edit_text(
            localized["options"], parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)  # Use "options" for consistency
        )

    elif data == "streak_cancel":
        await query.message.delete()

# Command to display leaderboard in Telegram bot
async def leaderboard_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.message.from_user.id
    chat = update.message.chat
    chat_id = str(chat.id)

    # Ensure this only works in group chats
    if chat.type == "private":
        return

    # Check if bot can operate
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        return

    # Check rate limit
    if is_rate_limited(user_id, "leaderboard"):
        group_settings = load_group_settings()
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        
        warning_message = await update.message.reply_text(localized["rate_limit"])
        context.job_queue.run_once(
            delete_message,
            when=5,
            chat_id=chat.id,
            data={"message_id": warning_message.message_id}
        )
        return

    # Load group settings and get language
    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Remove the languages button from the main menu
    keyboard = [
        [InlineKeyboardButton(localized["local_button"], callback_data="leaderboard_local")],
        [InlineKeyboardButton(localized["top_players_button"], callback_data="leaderboard_top_players"),
         InlineKeyboardButton(localized["top_groups_button"], callback_data="leaderboard_top_groups")],
        [InlineKeyboardButton(localized["close_button"], callback_data="leaderboard_cancel")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    await update.message.reply_text(
        localized["leaderboard_options"],
        reply_markup=reply_markup,
        parse_mode=ParseMode.HTML
    )


# Callback handler for leaderboard buttons
async def leaderboard_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    chat_id = query.message.chat_id
    user_id = query.from_user.id
    group_settings = load_group_settings()
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    if data == "leaderboard_local":
        if is_rate_limited(user_id, "leaderboard_local"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        leaderboard_image = await generate_leaderboard_image(chat_id)
        if leaderboard_image:
            sorted_players = load_leaderboard().get(str(chat_id), {}).get("players", {})
            sorted_players = sorted(sorted_players.items(), key=lambda x: x[1]["score"], reverse=True)[:MAX_PLAYERS]
            caption = localized["local_rankings_title"]
            for index, (player_id, data) in enumerate(sorted_players, start=1):
                emoji = get_emoji_for_user(player_id)
                caption += localized["local_player_entry"].format(
                    index=index, emoji=emoji, user_id=player_id, name=data["name"], score=data["score"]
                )
            try:
                await context.bot.send_photo(
                    chat_id=chat_id, photo=leaderboard_image, caption=caption, parse_mode=ParseMode.HTML,
                    protect_content=True, has_spoiler=True, read_timeout=30, write_timeout=30, connect_timeout=30
                )
            except telegram.error.TimedOut:
                await query.message.edit_text(localized["timeout_error"])
            except Exception as e:
                logger.error(f"Unexpected error: {e}")
                await query.message.edit_text(localized["generic_error"])
        else:
            await query.message.edit_text(localized["no_local_rankings"], parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]]))

    elif data == "leaderboard_top_players":
        top_players = get_top_players(limit=10)  # Limit to top 10
        if top_players:
            caption = localized["top_players_title"]
            for index, (player_id, data) in enumerate(top_players, start=1):
                emoji = get_emoji_for_user(player_id)
                caption += localized["top_player_entry"].format(
                    index=index,
                    emoji=emoji,
                    user_id=player_id,
                    name=data["name"],
                    score=data["score"]
                )
            keyboard = [
                [InlineKeyboardButton(localized["language"], callback_data="leaderboard_show_languages")],
                [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)
        else:
            await query.message.edit_text(
                localized["no_top_players"],
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]])
            )

    elif data == "leaderboard_show_languages":
        top_players = get_top_players(limit=10)  # Initial top players (all languages)
        caption = localized["top_players_title"]
        for index, (player_id, data) in enumerate(top_players, start=1):
            emoji = get_emoji_for_user(player_id)
            caption += localized["top_player_entry"].format(
                index=index,
                emoji=emoji,
                user_id=player_id,
                name=data["name"],
                score=data["score"]
            )
        flag_buttons = [
            InlineKeyboardButton(f"{localized['global_button1']}", callback_data="lang_top_overall"),
            InlineKeyboardButton("🇺🇸EN", callback_data="lang_top_en"),
            InlineKeyboardButton("🇪🇸ES", callback_data="lang_top_es"),
            InlineKeyboardButton("🇸🇦AR", callback_data="lang_top_ar"),
            InlineKeyboardButton("🇮🇷FA", callback_data="lang_top_fa"),
            InlineKeyboardButton("🇩🇪DE", callback_data="lang_top_de"),
            InlineKeyboardButton("🇫🇷FR", callback_data="lang_top_fr"),
            InlineKeyboardButton("🇮🇹IT", callback_data="lang_top_it"),
            InlineKeyboardButton("🇵🇹PT", callback_data="lang_top_pt"),
            InlineKeyboardButton("🇮🇩ID", callback_data="lang_top_id"),
            InlineKeyboardButton("🇰🇷KR", callback_data="lang_top_ko"),
            InlineKeyboardButton("🇷🇺RU", callback_data="lang_top_ru"),
            InlineKeyboardButton("🇹🇷TR", callback_data="lang_top_tr")
        ]
        keyboard = [
            [flag_buttons[0]],       # Overall button on its own row at the top
            flag_buttons[1:4],       # First row: 3 flags (EN, ES, AR)
            flag_buttons[4:7],       # Second row: 3 flags (FA, DE, FR)
            flag_buttons[7:10],      # Third row: 3 flags (IT, PT, ID)
            flag_buttons[10:13],     # Fourth row: 3 flags (KR, RU, TR)
            [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        if len(caption) > 4096:
            caption = caption[:4090] + "..."
        await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)

    elif data == "leaderboard_top_groups":
        top_groups = get_top_groups()
        if top_groups:
            caption = localized["top_groups_title"]
            for index, (group_id, data) in enumerate(top_groups, start=1):
                caption += localized["top_group_entry"].format(
                    index=index,
                    name=data["name"],
                    score=data["score"]
                )
            await query.message.edit_text(caption, parse_mode=ParseMode.HTML)
        else:
            await query.message.edit_text(
                localized["no_top_groups"],
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]])
            )

    elif data.startswith("lang_top_"):
        selected_option = data.split("_")[2]  # 'en', 'es', 'overall', etc.
        if selected_option == "overall":
            top_players = get_top_players(limit=10)  # Global top players
            caption = localized["top_players_title"]  # Overall title
            if top_players:
                for index, (player_id, data) in enumerate(top_players, start=1):
                    emoji = get_emoji_for_user(player_id)
                    caption += localized["top_player_entry"].format(
                        index=index,
                        emoji=emoji,
                        user_id=player_id,
                        name=data["name"],
                        score=data["score"]
                    )
            else:
                caption = localized["no_top_players"]

            # Simplified keyboard: only "Languages", "Back", and "Close" buttons
            keyboard = [
                [InlineKeyboardButton(localized["language"], callback_data="leaderboard_show_languages")],
                [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back"),
                 InlineKeyboardButton(localized["close_button"], callback_data="leaderboard_cancel")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)

        else:
            # Language-specific leaderboard (unchanged)
            top_players = get_top_players_by_language(selected_option)
            flag = LANGUAGE_FLAGS.get(selected_option, "🏳️")
            caption = localized["top_players_lang_title"].format(flag=flag)
            if top_players:
                for index, (player_id, data) in enumerate(top_players, start=1):
                    emoji = get_emoji_for_user(player_id)
                    caption += localized["top_player_entry"].format(
                        index=index,
                        emoji=emoji,
                        user_id=player_id,
                        name=data["name"],
                        score=data["score"]
                    )
            else:
                caption = localized["no_top_players_lang"].format(lang=selected_option.upper())

            flag_buttons = [
                InlineKeyboardButton(f"{localized['global_button1']} {'🔘' if selected_option == 'overall' else ''}", callback_data="lang_top_overall"),
                InlineKeyboardButton(f"🇺🇸EN {'🔘' if selected_option == 'en' else ''}", callback_data="lang_top_en"),
                InlineKeyboardButton(f"🇪🇸ES {'🔘' if selected_option == 'es' else ''}", callback_data="lang_top_es"),
                InlineKeyboardButton(f"🇸🇦AR {'🔘' if selected_option == 'ar' else ''}", callback_data="lang_top_ar"),
                InlineKeyboardButton(f"🇮🇷FA {'🔘' if selected_option == 'fa' else ''}", callback_data="lang_top_fa"),
                InlineKeyboardButton(f"🇩🇪DE {'🔘' if selected_option == 'de' else ''}", callback_data="lang_top_de"),
                InlineKeyboardButton(f"🇫🇷FR {'🔘' if selected_option == 'fr' else ''}", callback_data="lang_top_fr"),
                InlineKeyboardButton(f"🇮🇹IT {'🔘' if selected_option == 'it' else ''}", callback_data="lang_top_it"),
                InlineKeyboardButton(f"🇵🇹PT {'🔘' if selected_option == 'pt' else ''}", callback_data="lang_top_pt"),
                InlineKeyboardButton(f"🇮🇩ID {'🔘' if selected_option == 'id' else ''}", callback_data="lang_top_id"),
                InlineKeyboardButton(f"🇰🇷KR {'🔘' if selected_option == 'ko' else ''}", callback_data="lang_top_ko"),
                InlineKeyboardButton(f"🇷🇺RU {'🔘' if selected_option == 'ru' else ''}", callback_data="lang_top_ru"),
                InlineKeyboardButton(f"🇹🇷TR {'🔘' if selected_option == 'tr' else ''}", callback_data="lang_top_tr")
            ]
            keyboard = [
                [flag_buttons[0]],       # Overall button on its own row at the top
                flag_buttons[1:4],       # First row: 3 flags (EN, ES, AR)
                flag_buttons[4:7],       # Second row: 3 flags (FA, DE, FR)
                flag_buttons[7:10],      # Third row: 3 flags (IT, PT, ID)
                flag_buttons[10:13],     # Fourth row: 3 flags (KR, RU, TR)
                [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)

    elif data == "leaderboard_back":
        keyboard = [
            [InlineKeyboardButton(localized["local_button"], callback_data="leaderboard_local")],
            [InlineKeyboardButton(localized["top_players_button"], callback_data="leaderboard_top_players"),
             InlineKeyboardButton(localized["top_groups_button"], callback_data="leaderboard_top_groups")],
            [InlineKeyboardButton(localized["close_button"], callback_data="leaderboard_cancel")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await query.message.edit_text(
            localized["leaderboard_options"],
            reply_markup=reply_markup,
            parse_mode=ParseMode.HTML
        )

    elif data == "leaderboard_cancel":
        await query.message.delete()

    await query.answer()
    
# Settings Command
async def settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.message.chat
    user = update.message.from_user

    # Ensure this only works in group chats
    if chat.type == "private":
        return
    
    chat_id = str(chat.id)
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        return

    # Check if the user is an admin or owner
    chat_member = await context.bot.get_chat_member(chat.id, user.id)
    if chat_member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
        group_settings = load_group_settings()
        group_language = group_settings.get(str(chat.id), {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await update.message.reply_text(localized["admin_only"], parse_mode=ParseMode.HTML)
        return

    # Load group settings
    group_settings = load_group_settings()
    chat_id = str(chat.id)  # Ensure chat_id is a string

    # Initialize settings for this group if not present, including group name
    if chat_id not in group_settings:
        group_settings[chat_id] = {
            "group_name": chat.title,  # Add group name from chat object
            "answer_mode": "buttons",
            "quiz_interval": None,
            "language": "en"
        }
    # Update group name if it’s missing or has changed
    elif "group_name" not in group_settings[chat_id] or group_settings[chat_id]["group_name"] != chat.title:
        group_settings[chat_id]["group_name"] = chat.title

    # Save the updated settings
    await save_group_settings(group_settings)

    # Load language for the group
    group_language = group_settings[chat_id].get("language", "en")
    localized = localization.get(group_language, localization["en"])

    keyboard = [
        [InlineKeyboardButton(localized["interval_button"], callback_data="settings_set_interval"),
         InlineKeyboardButton(localized["reset_button"], callback_data="settings_reset_leaderboard")],
        [InlineKeyboardButton(localized["mode_button"], callback_data="settings_set_mode"),
         InlineKeyboardButton(localized["language_button"], callback_data="settings_language")],
        [InlineKeyboardButton(localized["close_button"], callback_data="settings_cancel")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    await update.message.reply_text(
        localized["menu"],
        reply_markup=reply_markup,
        parse_mode=ParseMode.HTML
    )

# Updated settings_callback function with debug logs
async def settings_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    chat_id = str(query.message.chat_id)  # Ensure chat_id is a string
    user_id = query.from_user.id

    # Check if the user is an admin or owner
    chat_member = await context.bot.get_chat_member(chat_id, user_id)
    if chat_member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
        group_settings = load_group_settings()
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await query.answer(localized["admin_only"], show_alert=True)
        return

    # Load group settings
    group_settings = load_group_settings()
    if chat_id not in group_settings:
        group_settings[chat_id] = {
            "group_name": query.message.chat.title,
            "answer_mode": "buttons",
            "quiz_interval": None,
            "language": "en"
        }

    # Update group name if missing or changed
    if "group_name" not in group_settings[chat_id] or group_settings[chat_id]["group_name"] != query.message.chat.title:
        group_settings[chat_id]["group_name"] = query.message.chat.title
        logger.info(f"Updated group name for chat {chat_id} to {query.message.chat.title}")

    # Get the group's language (default to "en")
    group_language = group_settings[chat_id].get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Handle settings changes
    if data == "settings_set_interval":
        current_interval = group_settings[chat_id].get("quiz_interval")
        keyboard = [
            [InlineKeyboardButton(localized["stop_quiz_button"], callback_data="settings_stop_quiz")],
            [InlineKeyboardButton(f"{'✅ ' if current_interval == 3600 else '›› '}{localized['interval_1hr']}", callback_data="interval_3600"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 7200 else '›› '}{localized['interval_2hrs']}", callback_data="interval_7200"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 10800 else '›› '}{localized['interval_3hrs']}", callback_data="interval_10800"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 14400 else '›› '}{localized['interval_4hrs']}", callback_data="interval_14400")],
            [InlineKeyboardButton(f"{'✅ ' if current_interval == 21600 else '›› '}{localized['interval_6hrs']}", callback_data="interval_21600"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 28800 else '›› '}{localized['interval_8hrs']}", callback_data="interval_28800"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 43200 else '›› '}{localized['interval_12hrs']}", callback_data="interval_43200"),
             InlineKeyboardButton(f"{'✅ ' if current_interval == 86400 else '›› '}{localized['interval_1day']}", callback_data="interval_86400")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["interval_prompt"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data.startswith("interval_"):
        interval = int(data.split("_")[1])
        group_settings[chat_id]["quiz_interval"] = interval
        await save_group_settings(group_settings)
        await schedule_quiz_jobs(context.job_queue, chat_id, interval)

        # Update the interval selection menu
        keyboard = [
            [InlineKeyboardButton(localized["stop_quiz_button"], callback_data="settings_stop_quiz")],
            [InlineKeyboardButton(f"{'✅ ' if interval == 3600 else '›› '}{localized['interval_1hr']}", callback_data="interval_3600"),
             InlineKeyboardButton(f"{'✅ ' if interval == 7200 else '›› '}{localized['interval_2hrs']}", callback_data="interval_7200"),
             InlineKeyboardButton(f"{'✅ ' if interval == 10800 else '›› '}{localized['interval_3hrs']}", callback_data="interval_10800"),
             InlineKeyboardButton(f"{'✅ ' if interval == 14400 else '›› '}{localized['interval_4hrs']}", callback_data="interval_14400")],
            [InlineKeyboardButton(f"{'✅ ' if interval == 21600 else '›› '}{localized['interval_6hrs']}", callback_data="interval_21600"),
             InlineKeyboardButton(f"{'✅ ' if interval == 28800 else '›› '}{localized['interval_8hrs']}", callback_data="interval_28800"),
             InlineKeyboardButton(f"{'✅ ' if interval == 43200 else '›› '}{localized['interval_12hrs']}", callback_data="interval_43200"),
             InlineKeyboardButton(f"{'✅ ' if interval == 86400 else '›› '}{localized['interval_1day']}", callback_data="interval_86400")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["interval_prompt"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_stop_quiz":
        # Remove existing jobs for this chat
        for name in [f"send_{chat_id}", f"send_{chat_id}_first"]:
            for job in context.job_queue.get_jobs_by_name(name):
                job.schedule_removal()
                logger.info(f"Removed job {name} for chat {chat_id}")
        await query.answer(localized["quiz_stopped"], show_alert=True)
        group_settings[chat_id]["quiz_interval"] = None
        await save_group_settings(group_settings)

        keyboard = [
            [InlineKeyboardButton(localized["stop_quiz_button"], callback_data="settings_stop_quiz")],
            [InlineKeyboardButton(f"›› {localized['interval_1hr']}", callback_data="interval_3600"),
             InlineKeyboardButton(f"›› {localized['interval_2hrs']}", callback_data="interval_7200"),
             InlineKeyboardButton(f"›› {localized['interval_3hrs']}", callback_data="interval_10800"),
             InlineKeyboardButton(f"›› {localized['interval_4hrs']}", callback_data="interval_14400")],
            [InlineKeyboardButton(f"›› {localized['interval_6hrs']}", callback_data="interval_21600"),
             InlineKeyboardButton(f"›› {localized['interval_8hrs']}", callback_data="interval_28800"),
             InlineKeyboardButton(f"›› {localized['interval_12hrs']}", callback_data="interval_43200"),
             InlineKeyboardButton(f"›› {localized['interval_1day']}", callback_data="interval_86400")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["interval_prompt"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_reset_leaderboard":
        keyboard = [
            [InlineKeyboardButton(localized["yes_button"], callback_data="confirm_reset_yes"),
             InlineKeyboardButton(localized["no_button"], callback_data="confirm_reset_no")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await query.message.edit_text(
            localized["reset_confirm_prompt"],
            reply_markup=reply_markup,
            parse_mode=ParseMode.HTML
        )

    elif data == "confirm_reset_yes":
        if await reset_leaderboard(chat_id):
            await query.answer(localized["reset_success"], show_alert=True)
        else:
            await query.answer(localized["reset_fail"], show_alert=True)
        
        keyboard = [
            [InlineKeyboardButton(localized["interval_button"], callback_data="settings_set_interval"),
             InlineKeyboardButton(localized["reset_button"], callback_data="settings_reset_leaderboard")],
            [InlineKeyboardButton(localized["mode_button"], callback_data="settings_set_mode"),
             InlineKeyboardButton(localized["language_button"], callback_data="settings_language")],
            [InlineKeyboardButton(localized["close_button"], callback_data="settings_cancel")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await query.message.edit_text(
            localized["menu"],
            reply_markup=reply_markup,
            parse_mode=ParseMode.HTML
        )

    elif data == "confirm_reset_no":
        keyboard = [
            [InlineKeyboardButton(localized["interval_button"], callback_data="settings_set_interval"),
             InlineKeyboardButton(localized["reset_button"], callback_data="settings_reset_leaderboard")],
            [InlineKeyboardButton(localized["mode_button"], callback_data="settings_set_mode"),
             InlineKeyboardButton(localized["language_button"], callback_data="settings_language")],
            [InlineKeyboardButton(localized["close_button"], callback_data="settings_cancel")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await query.message.edit_text(
            localized["menu"],
            reply_markup=reply_markup,
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_set_mode":
        current_mode = group_settings[chat_id].get("answer_mode")
        keyboard = [
            [InlineKeyboardButton(f"{'✅ ' if current_mode == 'buttons' else '›› '}{localized['mode_buttons']}", callback_data="answer_mode_buttons"),
             InlineKeyboardButton(f"{'✅ ' if current_mode == 'write' else '›› '}{localized['mode_write']}", callback_data="answer_mode_write")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["mode_prompt"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data.startswith("answer_mode_"):
        mode = data.split("_")[2]
        group_settings[chat_id]["answer_mode"] = mode
        await save_group_settings(group_settings)

        keyboard = [
            [InlineKeyboardButton(f"{'✅ ' if mode == 'buttons' else '›› '}{localized['mode_buttons']}", callback_data="answer_mode_buttons"),
             InlineKeyboardButton(f"{'✅ ' if mode == 'write' else '›› '}{localized['mode_write']}", callback_data="answer_mode_write")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["mode_prompt"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_language":
        current_language = group_settings[chat_id].get("language", "en")
        keyboard = [
            [InlineKeyboardButton(f"{'✅ ' if current_language == 'en' else '›› '}🇺🇸EN", callback_data="language_en"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'es' else '›› '}🇪🇸ES", callback_data="language_es"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'ar' else '›› '}🇸🇦AR", callback_data="language_ar")],
            [InlineKeyboardButton(f"{'✅ ' if current_language == 'fa' else '›› '}🇮🇷FA", callback_data="language_fa"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'de' else '›› '}🇩🇪DE", callback_data="language_de"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'fr' else '›› '}🇫🇷FR", callback_data="language_fr")],
            [InlineKeyboardButton(f"{'✅ ' if current_language == 'it' else '›› '}🇮🇹IT", callback_data="language_it"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'pt' else '›› '}🇵🇹PT", callback_data="language_pt"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'id' else '›› '}🇮🇩ID", callback_data="language_id")],
            [InlineKeyboardButton(f"{'✅ ' if current_language == 'ko' else '›› '}🇰🇷KR", callback_data="language_ko"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'ru' else '›› '}🇷🇺RU", callback_data="language_ru"),
             InlineKeyboardButton(f"{'✅ ' if current_language == 'tr' else '›› '}🇹🇷TR", callback_data="language_tr")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["language_message"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data.startswith("language_"):
        language = data.split("_")[1]
        logger.info(f"Setting language to {language} for chat_id {chat_id}")
        group_settings[chat_id]["language"] = language
        await save_group_settings(group_settings)
        logger.info(f"Updated group_settings: {group_settings[chat_id]}")

        # Refresh localized strings with the new language
        localized = localization.get(language, localization["en"])
        keyboard = [
            [InlineKeyboardButton(f"{'✅ ' if language == 'en' else '›› '}🇺🇸EN", callback_data="language_en"),
             InlineKeyboardButton(f"{'✅ ' if language == 'es' else '›› '}🇪🇸ES", callback_data="language_es"),
             InlineKeyboardButton(f"{'✅ ' if language == 'ar' else '›› '}🇸🇦AR", callback_data="language_ar")],
            [InlineKeyboardButton(f"{'✅ ' if language == 'fa' else '›› '}🇮🇷FA", callback_data="language_fa"),
             InlineKeyboardButton(f"{'✅ ' if language == 'de' else '›› '}🇩🇪DE", callback_data="language_de"),
             InlineKeyboardButton(f"{'✅ ' if language == 'fr' else '›› '}🇫🇷FR", callback_data="language_fr")],
            [InlineKeyboardButton(f"{'✅ ' if language == 'it' else '›› '}🇮🇹IT", callback_data="language_it"),
             InlineKeyboardButton(f"{'✅ ' if language == 'pt' else '›› '}🇵🇹PT", callback_data="language_pt"),
             InlineKeyboardButton(f"{'✅ ' if language == 'id' else '›› '}🇮🇩ID", callback_data="language_id")],
            [InlineKeyboardButton(f"{'✅ ' if language == 'ko' else '›› '}🇰🇷KR", callback_data="language_ko"),
             InlineKeyboardButton(f"{'✅ ' if language == 'ru' else '›› '}🇷🇺RU", callback_data="language_ru"),
             InlineKeyboardButton(f"{'✅ ' if language == 'tr' else '›› '}🇹🇷TR", callback_data="language_tr")],
            [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
        ]
        await query.message.edit_text(
            localized["language_message"],
            reply_markup=InlineKeyboardMarkup(keyboard),
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_back":
        group_language = group_settings[chat_id].get("language", "en")
        localized = localization.get(group_language, localization["en"])
        keyboard = [
            [InlineKeyboardButton(localized["interval_button"], callback_data="settings_set_interval"),
             InlineKeyboardButton(localized["reset_button"], callback_data="settings_reset_leaderboard")],
            [InlineKeyboardButton(localized["mode_button"], callback_data="settings_set_mode"),
             InlineKeyboardButton(localized["language_button"], callback_data="settings_language")],
            [InlineKeyboardButton(localized["close_button"], callback_data="settings_cancel")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        await query.message.edit_text(
            localized["menu"],
            reply_markup=reply_markup,
            parse_mode=ParseMode.HTML
        )

    elif data == "settings_cancel":
        await query.message.delete()

    await query.answer()


#Report question command       
async def report_question(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.message.chat
    user = update.message.from_user
    chat_id = str(chat.id)
    user_id = str(user.id)

    # Ensure this only works in group chats
    if chat.type == "private":
        return

    # Check if bot can operate
    can_operate, message = await can_bot_operate(chat_id, context)
    if not can_operate:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        return

    replied_to = update.message.reply_to_message
    if not replied_to:
        group_settings = load_group_settings()
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await update.message.reply_text(localized["report_no_reply"], parse_mode=ParseMode.HTML)
        return

    # Check if the replied-to message is a quiz question (photo + caption)
    if not (replied_to.photo and replied_to.caption):
        group_settings = load_group_settings()
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await update.message.reply_text(localized["report_not_question"], parse_mode=ParseMode.HTML)
        return

    # Attempt to retrieve question data if it exists in active_questions
    question_key = f"{chat_id}_{replied_to.message_id}"
    question_data = active_questions.get(question_key, {})
    question_type = question_data.get("type", "unknown")
    correct_answers = question_data.get("correct_answers", ["Unknown"])
    question_number = question_data.get("question_number", "Unknown")  # Retrieve question number

    # Adjust question type from "taylor" to "Lore" or keep as is
    display_question_type = "Lore" if question_type == "taylor" else question_type.capitalize()

    group_settings = load_group_settings()
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Get the original message details directly from replied_to
    image_file_id = replied_to.photo[-1].file_id if replied_to.photo else None
    caption = replied_to.caption or "No caption"

    # Sanitize inputs to prevent HTML parsing issues
    safe_user_name = sanitize_input(user.first_name)
    safe_group_name = sanitize_input(chat.title)
    safe_caption = sanitize_input(caption)
    safe_correct_answers = [sanitize_input(ans) for ans in correct_answers]
    safe_question_number = sanitize_input(str(question_number))  # Sanitize question number

    # Use original dynamic date formatting
    current_date = time.strftime('%Y-%m-%d', time.gmtime())

    # Prepare report message with bold labels using HTML, including question number
    report_message = (
        "📢 <b>Question Reported</b>\n\n"
        f"👤 <b>Reported by:</b> {safe_user_name}\n"
        f"🏠 <b>Group:</b> {safe_group_name}\n"
        f"❓ <b>Question Type:</b> {display_question_type}\n"
        f"🔢 <b>Question Number:</b> {safe_question_number}\n"
        f"📅 <b>Reported on:</b> {current_date}"
    )

    # Log the message for debugging
    logger.info(f"Attempting to send report message: {report_message}")

    try:
        if image_file_id:
            await context.bot.send_photo(
                chat_id=REPORT_GROUP_ID,
                photo=image_file_id,
                caption=report_message,
                parse_mode=ParseMode.HTML,
                protect_content=True,
                has_spoiler=True
            )
        else:
            await context.bot.send_message(
                chat_id=REPORT_GROUP_ID,
                text=report_message,
                parse_mode=ParseMode.HTML,
                protect_content=True,
                has_spoiler=True
            )
        logger.info(f"Question {question_key} reported by user {user_id} and sent to {REPORT_GROUP_ID}")
    except Exception as e:
        logger.error(f"Failed to send reported question details: {e}")
        await update.message.reply_text(localized["report_error"], parse_mode=ParseMode.HTML)
        return

    await update.message.reply_text(localized["report_success"], parse_mode=ParseMode.HTML)
    # Optionally mark as reported if still in active_questions
    if question_key in active_questions:
        question_data["reported"] = True
    
    
#Error Handler
async def error_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    logger.error(f"Exception occurred: {context.error}", exc_info=True)


#handle bot when added to the group
async def handle_bot_added(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle the event when the bot is added to a group, using the adding user's language."""
    chat = update.message.chat
    if chat.type not in ["group", "supergroup"]:
        return  # Ignore if not a group or supergroup

    new_members = update.message.new_chat_members
    if not new_members:
        return  # No new members to process

    bot_id = context.bot.id
    bot_username = context.bot.username

    # Check if the bot is among the new members
    if any(member.id == bot_id for member in new_members):
        # Get the user who added the bot
        adding_user = update.message.from_user
        if not adding_user:
            logger.warning("Could not determine the user who added the bot.")
            return

        user_id = str(adding_user.id)
        chat_id = str(chat.id)

        # Load the user's language preference from private chat (default to "en")
        global user_languages
        user_language = user_languages.get(user_id, "en")
        localized = localization.get(user_language, localization["en"])
        logger.info(f"Bot added to group {chat_id} by user {user_id} with language {user_language}")

        # Check if the group is banned
        if chat_id in BANNED_GROUPS:
            group_name = BANNED_GROUPS[chat_id]
            logger.info(f"Bot added to banned group {chat_id} ({group_name})")
            try:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=localized["banned_group_message"],
                    parse_mode=ParseMode.HTML,
                    disable_web_page_preview=False
                )
                logger.info(f"Sent banned group message to {chat_id}")
                # Attempt to leave the group
                await context.bot.leave_chat(chat_id)
                logger.info(f"Bot left banned group {chat_id} ({group_name})")
            except Exception as e:
                logger.error(f"Failed to send message or leave banned group {chat_id} ({group_name}): {e}")
            return

        # Check if bot can operate (minimum member count)
        can_operate, message = await can_bot_operate(chat_id, context)
        if not can_operate:
            try:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=message,
                    parse_mode=ParseMode.HTML,
                    disable_web_page_preview=False
                )
                logger.info(f"Sent min members message to group {chat_id}")
            except Exception as e:
                logger.error(f"Failed to send min members message to group {chat_id}: {e}")
            return

        # Load and initialize group settings
        group_settings = load_group_settings()
        if chat_id not in group_settings:
            group_settings[chat_id] = {
                "group_name": chat.title,
                "answer_mode": "buttons",
                "quiz_interval": None,
                "language": "en"
            }
            await save_group_settings(group_settings)
            logger.info(f"Initialized settings for new group {chat_id}: {group_settings[chat_id]}")

        # Welcome message using the adding user's language
        welcome_message = localized["group_welcome"]
        keyboard = [
            [InlineKeyboardButton("𝑻𝒂𝒚𝒍𝒐𝒓 𝑺𝒘𝒊𝒇𝒕 𝑵𝒂𝒕𝒊𝒐𝒏 ✨", url="t.me/missamericanatsn")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)

        try:
            await context.bot.send_message(
                chat_id=chat.id,
                text=welcome_message,
                parse_mode=ParseMode.HTML,
                reply_markup=reply_markup
            )
            logger.info(f"Sent welcome message to group {chat_id} in language {user_language}")
        except Exception as e:
            logger.error(f"Failed to send welcome message to group {chat_id}: {e}")

        
#laguage callback
async def language_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global user_languages  # Declare global at the very start
    
    query = update.callback_query
    data = query.data
    user_id = str(query.from_user.id)  # Ensure user_id is a string
    chat_id = str(query.message.chat_id)  # Ensure chat_id is a string
    first_name = query.from_user.first_name  # Get user's first name
    bot_username = context.bot.username  # Get bot username for button URL
    logger.info(f"Language callback triggered with data: {data}")

    try:
        # Determine if this is a group settings change or private start command
        is_group = query.message.chat.type != "private"

        if data == "language_select":
            # For private chats: show language selection menu
            current_language = user_languages.get(user_id, "en")  # Load from SQLite, default to "en"
            localized = localization.get(current_language, localization["en"])
            keyboard = [
                [InlineKeyboardButton(f"🇺🇸EN {'🔘' if current_language == 'en' else ''}", callback_data="set_language_en"),
                 InlineKeyboardButton(f"🇪🇸ES {'🔘' if current_language == 'es' else ''}", callback_data="set_language_es"),
                 InlineKeyboardButton(f"🇸🇦AR {'🔘' if current_language == 'ar' else ''}", callback_data="set_language_ar")],
                [InlineKeyboardButton(f"🇮🇷FA {'🔘' if current_language == 'fa' else ''}", callback_data="set_language_fa"),
                 InlineKeyboardButton(f"🇩🇪DE {'🔘' if current_language == 'de' else ''}", callback_data="set_language_de"),
                 InlineKeyboardButton(f"🇫🇷FR {'🔘' if current_language == 'fr' else ''}", callback_data="set_language_fr")],
                [InlineKeyboardButton(f"🇮🇹IT {'🔘' if current_language == 'it' else ''}", callback_data="set_language_it"),
                 InlineKeyboardButton(f"🇵🇹PT {'🔘' if current_language == 'pt' else ''}", callback_data="set_language_pt"),
                 InlineKeyboardButton(f"🇮🇩ID {'🔘' if current_language == 'id' else ''}", callback_data="set_language_id")],
                [InlineKeyboardButton(f"🇰🇷KR {'🔘' if current_language == 'ko' else ''}", callback_data="set_language_ko"),
                 InlineKeyboardButton(f"🇷🇺RU {'🔘' if current_language == 'ru' else ''}", callback_data="set_language_ru"),
                 InlineKeyboardButton(f"🇹🇷TR {'🔘' if current_language == 'tr' else ''}", callback_data="set_language_tr")],
                [InlineKeyboardButton(localized["back_button"], callback_data="language_back")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            await query.message.edit_text(
                text=localized.get("language_message"),
                reply_markup=reply_markup,
                parse_mode="HTML"
            )

        elif data.startswith("set_language_"):
            language = data.split("_")[2]
            logger.info(f"Setting language to {language} for user_id {user_id} in chat_id {chat_id}")

            if is_group:
                # Group settings: update group language
                group_settings = load_group_settings()
                group_settings[chat_id]["language"] = language
                await save_group_settings(group_settings)  # Use async save
                logger.info(f"Updated group settings: {group_settings[chat_id]}")

                # Reload localized strings with new language
                localized = localization.get(language, localization["en"])
                keyboard = [
                    [InlineKeyboardButton(f"🇺🇸EN {'🔘' if language == 'en' else ''}", callback_data="set_language_en"),
                     InlineKeyboardButton(f"🇪🇸ES {'🔘' if language == 'es' else ''}", callback_data="set_language_es"),
                     InlineKeyboardButton(f"🇸🇦AR {'🔘' if language == 'ar' else ''}", callback_data="set_language_ar")],
                    [InlineKeyboardButton(f"🇮🇷FA {'🔘' if language == 'fa' else ''}", callback_data="set_language_fa"),
                     InlineKeyboardButton(f"🇩🇪DE {'🔘' if language == 'de' else ''}", callback_data="set_language_de"),
                     InlineKeyboardButton(f"🇫🇷FR {'🔘' if language == 'fr' else ''}", callback_data="set_language_fr")],
                    [InlineKeyboardButton(f"🇮🇹IT {'🔘' if language == 'it' else ''}", callback_data="set_language_it"),
                     InlineKeyboardButton(f"🇵🇹PT {'🔘' if language == 'pt' else ''}", callback_data="set_language_pt"),
                     InlineKeyboardButton(f"🇮🇩ID {'🔘' if language == 'id' else ''}", callback_data="set_language_id")],
                    [InlineKeyboardButton(f"🇰🇷KR {'🔘' if language == 'ko' else ''}", callback_data="set_language_ko"),
                     InlineKeyboardButton(f"🇷🇺RU {'🔘' if language == 'ru' else ''}", callback_data="set_language_ru"),
                     InlineKeyboardButton(f"🇹🇷TR {'🔘' if language == 'tr' else ''}", callback_data="set_language_tr")],
                    [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
                ]
                reply_markup = InlineKeyboardMarkup(keyboard)
                await query.message.edit_text(
                    localized["language_message"],
                    reply_markup=reply_markup,
                    parse_mode="HTML"
                )
            else:
                # Private chat: update user language
                user_languages[user_id] = language
                await save_user_languages(user_languages)  # Save to SQLite
                logger.info(f"Updated user language for {user_id} to {language}")

                # Load localized strings for the new language
                localized = localization.get(language, localization["en"])

                # Format the welcome message with first_name and user_id
                caption = localized["welcome"].format(
                    first_name=first_name,
                    user_id=user_id
                )

                # Define buttons, including emoji selection
                keyboard = [
                    [InlineKeyboardButton(localized["add_to_group"], url=f"https://t.me/{bot_username}?startgroup=true")],
                    [InlineKeyboardButton(localized["support"], url="https://t.me/MastermindBotSupport"),
                     InlineKeyboardButton(localized["updates"], url="https://t.me/MastermindBotUpdates")],
                    [InlineKeyboardButton(localized["language"], callback_data="language_select"),
                     InlineKeyboardButton(localized["emoji_select_button"], callback_data="emoji_select")]
                ]
                reply_markup = InlineKeyboardMarkup(keyboard)

                # Edit the existing message to show the updated welcome message
                await query.message.edit_text(
                    text=caption,
                    parse_mode="HTML",
                    reply_markup=reply_markup,
                    disable_web_page_preview=False
                )

        elif data == "language_back":
            current_language = user_languages.get(user_id, "en")  # Load from SQLite
            localized = localization.get(current_language, localization["en"])
            # Format the welcome message for the back action
            caption = localized["welcome"].format(
                first_name=first_name,
                user_id=user_id
            )
            keyboard = [
                [InlineKeyboardButton(localized["add_to_group"], url=f"https://t.me/{bot_username}?startgroup=true")],
                [InlineKeyboardButton(localized["support"], url="https://t.me/MastermindBotSupport"),
                 InlineKeyboardButton(localized["updates"], url="https://t.me/MastermindBotUpdates")],
                [InlineKeyboardButton(localized["language"], callback_data="language_select"),
                 InlineKeyboardButton(localized["emoji_select_button"], callback_data="emoji_select")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            # Edit the existing message to show the welcome message
            await query.message.edit_text(
                text=caption,
                parse_mode="HTML",
                reply_markup=reply_markup,
                disable_web_page_preview=False
            )

        await query.answer()
    except Exception as e:
        logger.error(f"Error in language_callback: {e}")
        await query.answer(f"❌ An error occurred: {str(e)}", show_alert=True)


# Handlers
def setup_handlers(application):
    application.add_handler(CommandHandler("start", start, filters.ChatType.PRIVATE))
    application.add_handler(CommandHandler("leaderboard", leaderboard_command, filters.ChatType.GROUPS))
    application.add_handler(CommandHandler("settings", settings, filters.ChatType.GROUPS))
    application.add_handler(CommandHandler("streak", streak_command, filters.ChatType.GROUPS))
    application.add_handler(CommandHandler("profile", profile))
    application.add_handler(CommandHandler("reportquestion", report_question, filters.ChatType.GROUPS))
    application.add_handler(CommandHandler("stats", stats_command, filters.ChatType.GROUPS))
    application.add_handler(CallbackQueryHandler(settings_callback, pattern="^settings_|^interval_|^answer_mode_|^language_[a-z]{2}$|^confirm_reset_"))
    application.add_handler(CallbackQueryHandler(handle_answer, pattern="^answer_"))
    application.add_handler(CallbackQueryHandler(leaderboard_callback, pattern="^leaderboard_|^lang_top_"))
    application.add_handler(CallbackQueryHandler(streak_callback, pattern="^streak_|^lang_streak_"))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_answer))
    application.add_handler(CallbackQueryHandler(language_callback, pattern="^set_language_|^language_select|^language_back"))
    application.add_handler(CallbackQueryHandler(emoji_callback, pattern="^emoji_select$|^set_emoji_|^emoji_back$"))
    application.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, handle_bot_added))
    application.add_error_handler(error_handler)
    
#SEND QUESTION DELAYS FIX
scheduler = AsyncIOScheduler()
scheduler.configure({'misfire_grace_time': 90})  # Allow 90 seconds grace period
application.job_queue.scheduler = scheduler

#main        
async def main():
    global leaderboard_data, global_leaderboard, streak_data, achievements_data, user_languages, USER_EMOJIS
    try:
        logger.info("Starting MastermindBot")
        logger.info(f"Using BOT_TOKEN: {BOT_TOKEN[:10]}...")

        logger.info("Initializing database")
        init_database()
        logger.info("Loading leaderboard data")
        leaderboard_data = load_leaderboard()
        logger.info("Loading global leaderboard")
        global_leaderboard = load_global_leaderboard()
        logger.info("Loading streak data")
        streak_data = load_streak_data()
        logger.info("Loading achievements data")
        achievements_data = load_achievements_data()
        logger.info(f"Loaded achievements_data: {achievements_data}")
        logger.info("Loading user languages")
        user_languages = load_user_languages()
        logger.info("Loading user emojis")
        USER_EMOJIS.update(load_user_emojis())
        logger.info(f"Loaded {len(USER_EMOJIS)} user emojis from SQLite")
        logger.info("Setting bot commands")
        set_bot_commands()
        logger.info("Loading templates")
        load_templates()
        logger.info("Loading group settings")
        group_settings = load_group_settings()
        logger.info(f"Loaded settings for {len(group_settings)} groups: {group_settings}")

        logger.info("Configuring scheduler")
        scheduler = AsyncIOScheduler()
        scheduler.configure({'misfire_grace_time': 600})  # Increased to 600 seconds
        application.job_queue.scheduler = scheduler

        logger.info("Clearing existing jobs")
        for job in application.job_queue.jobs():
            job.schedule_removal()
            logger.info(f"Cleared job {job.name}")

        logger.info("Scheduling group jobs")
        async with GLOBAL_SCHEDULING_LOCK:
            for chat_id, settings in group_settings.items():
                interval = settings.get("quiz_interval")
                if not interval:
                    logger.info(f"No quiz interval for chat {chat_id}")
                    continue
                await schedule_quiz_jobs(application.job_queue, chat_id, interval)

        logger.info("Starting job monitoring task")
        asyncio.create_task(log_active_jobs(application.job_queue))

        logger.info("Setting up handlers")
        setup_handlers(application)

        logger.info("Starting Telethon client")
        try:
            await client.start(bot_token=BOT_TOKEN)
            logger.info("Telethon client started successfully")
        except Exception as e:
            logger.error(f"Failed to start Telethon client: {e}")
            raise

        logger.info("Initializing application")
        await application.initialize()
        logger.info("Starting application")
        await application.start()
        logger.info("Starting polling")
        await application.updater.start_polling()
        logger.info("Bot is running")

        logger.info("Entering keep-alive loop")
        while True:
            await asyncio.sleep(3600)
    except asyncio.CancelledError:
        logger.info("Bot shutdown requested")
    except Exception as e:
        logger.error(f"Unexpected error in main(): {e}")
        raise
    finally:
        logger.info("Shutting down")
        await shutdown(None, asyncio.get_running_loop())

async def shutdown(signum, loop):
    logger.info(f"Received signal {signum}. Shutting down...")
    try:
        # Save all critical data using in-memory states
        await save_leaderboard(leaderboard_data)
        await save_global_leaderboard(global_leaderboard)
        await save_streak_data(streak_data)
        await save_achievements_data(achievements_data)

        # Stop and shutdown the application if running
        if application.running:
            await application.stop()
            await application.shutdown()
            logger.info("Telegram application shut down.")

        # Disconnect the Telethon client if connected
        if client.is_connected():
            await client.disconnect()
            logger.info("Telethon client disconnected.")

        # Cancel all pending tasks except the current one
        tasks = [t for t in asyncio.all_tasks(loop) if not t.done() and t is not asyncio.current_task()]
        if tasks:
            logger.info(f"Cancelling {len(tasks)} pending tasks...")
            for task in tasks:
                logger.info(f"Cancelling task: {task.get_name()}")
                task.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)

    except asyncio.CancelledError:
        logger.info("Shutdown completed with cancelled tasks.")
    except Exception as e:
        logger.error(f"Error during shutdown: {e}")
    finally:
        if not loop.is_closed():
            loop.stop()
        logger.info("Event loop stopped.")

def signal_handler(signum, frame):
    try:
        loop = asyncio.get_running_loop()
        asyncio.create_task(shutdown(signum, loop))
    except RuntimeError:
        pass

if __name__ == "__main__":
    try:
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGTERM, signal_handler)
        loop.run_until_complete(main())
    except KeyboardInterrupt:
        logger.info("Received KeyboardInterrupt. Shutting down...")
    except Exception as e:
        logger.error(f"Unexpected error: {e}")
    finally:
        if not loop.is_closed():
            loop.run_until_complete(shutdown(None, loop))
        loop.close()
        logger.info("Event loop closed.")
