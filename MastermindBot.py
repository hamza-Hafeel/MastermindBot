import telegram
from aiolimiter import AsyncLimiter
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from telegram.error import TimedOut, RetryAfter
from telethon import TelegramClient
from telethon.tl.functions.messages import SendReactionRequest
from telethon.tl.types import ReactionEmoji
from datetime import datetime, timezone
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
    filters,
    ChatMemberHandler
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
import ssl
import certifi
import hashlib
import asyncpg
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

# Load config.json with PostgreSQL connection details
try:
    logger.debug("Loading config.json")
    with open("config.json", "r") as file:
        config = json.load(file)
        BOT_TOKEN = config["BOT_TOKEN"]
        API_ID = config["API_ID"]
        API_HASH = config["API_HASH"]
        REPORT_GROUP_ID = config["REPORT_GROUP_ID"]
        POSTGRES_DSN = config.get("POSTGRES_DSN", "postgresql://user:password@localhost:5432/bot_data")
    logger.debug(f"Successfully loaded config.json with BOT_TOKEN: {BOT_TOKEN[:10]}...")
except Exception as e:
    logger.error(f"Failed to load config.json: {e}")
    sys.exit(1)

# Load banned groups
try:
    logger.debug("Loading banned_groups.json")
    with open("banned_groups.json", "r") as file:
        banned_groups_config = json.load(file)
        # Validate structure
        if not isinstance(banned_groups_config, dict) or "banned_groups" not in banned_groups_config:
            raise ValueError("Invalid banned_groups.json structure")
        banned_groups_list = banned_groups_config["banned_groups"]
        if not isinstance(banned_groups_list, list):
            raise ValueError("banned_groups must be a list")
        BANNED_GROUPS = {}
        for group in banned_groups_list:
            if isinstance(group, dict) and "chat_id" in group and "name" in group:
                BANNED_GROUPS[str(group["chat_id"])] = group["name"]
        logger.debug(f"Successfully loaded banned_groups.json with {len(BANNED_GROUPS)} groups: {BANNED_GROUPS}")
except Exception as e:
    logger.error(f"Failed to load banned_groups.json: {e}")
    BANNED_GROUPS = {}  # Fallback to empty dict if loading fails
    logger.debug("Initialized empty BANNED_GROUPS due to load failure")

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

# Async PostgreSQL connection pool
async def create_db_pool():
    try:
        pool = await asyncpg.create_pool(dsn=POSTGRES_DSN, min_size=5, max_size=20)
        logger.info("PostgreSQL connection pool created successfully")
        return pool
    except Exception as e:
        logger.error(f"Failed to create PostgreSQL connection pool: {e}")
        sys.exit(1)

# Global variables for data structures
active_questions = {}
quiz_intervals = {}
leaderboard_data = {}
global_leaderboard = {}
streak_data = {}
achievements_data = {}
user_languages = {}
USER_EMOJIS = {}
question_cache = {}
CHAT_SEND_LOCKS = defaultdict(asyncio.Lock)
answer_modes = {}  # Store answer modes for each chat
IMAGE_GEN_SEMAPHORE = asyncio.Semaphore(5)  # Limit to 5 concurrent image generations
BASE_TEMPLATES = {}  # Cache for preloaded leaderboard templates
BASE_STREAK_TEMPLATES = {} # Cache for preloaded streak templates
STREAK_IMAGE_CACHE = {}
LEADERBOARD_IMAGE_CACHE = {}  # Cache for leaderboard images
GROUPS_PER_SECOND = 200
CHAT_LOCKS = {}
ACHIEVEMENTS_DATA_LOCK = asyncio.Lock()
MAX_PLAYERS = 10  # Show top 10 players
SEND_RATE_LIMITER = AsyncLimiter(GROUPS_PER_SECOND, 1)
GLOBAL_SCHEDULING_LOCK = asyncio.Lock()

# In-memory queue for batching database writes
DB_WRITE_QUEUE = asyncio.Queue()

# Async context manager for database connections
@asynccontextmanager
async def get_db_connection(pool):
    async with pool.acquire() as conn:
        try:
            yield conn
        finally:
            pass  # Connection is managed by the pool

# Initialize the database with tables
async def init_database(pool):
    async with get_db_connection(pool) as conn:
        try:
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS leaderboard (
                    chat_id TEXT,
                    user_id TEXT,
                    name TEXT,
                    score INTEGER,
                    PRIMARY KEY (chat_id, user_id)
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS global_leaderboard (
                    user_id TEXT PRIMARY KEY,
                    name TEXT,
                    score INTEGER
                )
            """)
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS global_leaderboard_groups (
                    user_id TEXT,
                    group_id TEXT,
                    group_name TEXT,
                    score INTEGER,
                    PRIMARY KEY (user_id, group_id),
                    FOREIGN KEY (user_id) REFERENCES global_leaderboard(user_id)
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS streaks (
                    chat_id TEXT,
                    user_id TEXT,
                    name TEXT,
                    streak INTEGER,
                    PRIMARY KEY (chat_id, user_id)
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS achievements (
                    user_id TEXT,
                    achievement_id TEXT,
                    PRIMARY KEY (user_id, achievement_id)
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS user_stats (
                    user_id TEXT PRIMARY KEY,
                    correct_answers INTEGER DEFAULT 0,
                    current_streak INTEGER DEFAULT 0,
                    highest_streak INTEGER DEFAULT 0,
                    quick_answers INTEGER DEFAULT 0,
                    taylor_answers INTEGER DEFAULT 0,
                    lyrics_answers INTEGER DEFAULT 0,
                    incorrect_answers INTEGER DEFAULT 0,
                    groups_participated INTEGER DEFAULT 0,
                    total_points INTEGER DEFAULT 0
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS user_languages (
                    user_id TEXT PRIMARY KEY,
                    language TEXT DEFAULT 'en'
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS user_emojis (
                    user_id TEXT PRIMARY KEY,
                    name TEXT,
                    emoji TEXT DEFAULT '👤',
                    created_at TEXT
                )
            """)
            
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS group_settings (
                    chat_id TEXT PRIMARY KEY,
                    group_name TEXT,
                    answer_mode TEXT DEFAULT 'buttons',
                    quiz_interval INTEGER,
                    language TEXT DEFAULT 'en'
                )
            """)

            await conn.execute("""
                CREATE TABLE IF NOT EXISTS bot_groups (
                    chat_id TEXT PRIMARY KEY,
                    group_name TEXT
                )
            """)
            
            logger.info("PostgreSQL database initialized.")
        except Exception as e:
            logger.error(f"Failed to initialize PostgreSQL database: {e}")
            raise

async def batch_write_to_db(pool):
    """Process queued database writes in batches with retry logic."""
    while True:
        try:
            if DB_WRITE_QUEUE.empty():
                await asyncio.sleep(1)
                continue

            queries = []
            max_batch_size = 100
            while not DB_WRITE_QUEUE.empty() and len(queries) < max_batch_size:
                try:
                    query, params = DB_WRITE_QUEUE.get_nowait()
                    queries.append((query, params))
                    DB_WRITE_QUEUE.task_done()
                except asyncio.QueueEmpty:
                    break

            if not queries:
                await asyncio.sleep(1)
                continue

            async with pool.acquire() as conn:
                async with conn.transaction():
                    for query, params in queries:
                        max_retries = 3
                        for attempt in range(max_retries):
                            try:
                                await conn.execute(query, *params)
                                break
                            except Exception as e:
                                if attempt == max_retries - 1:
                                    logger.error(f"Failed to execute query after {max_retries} attempts: {query} | Params: {params} | Error: {e}")
                                    continue
                                await asyncio.sleep(0.5 * (2 ** attempt))
            logger.info(f"Processed {len(queries)} batch writes")
        except Exception as e:
            logger.error(f"Error in batch_write_to_db: {e}")
        await asyncio.sleep(1)


async def initialize_user_emojis(db_pool):
    """Load user emojis from the database into USER_EMOJIS at startup."""
    global USER_EMOJIS
    async with db_pool.acquire() as conn:
        records = await conn.fetch("SELECT user_id, name, emoji, created_at FROM user_emojis")
        for record in records:
            USER_EMOJIS[record["user_id"]] = {
                "name": record["name"],
                "emoji": record["emoji"],
                "created_at": record["created_at"]
            }
        logger.info(f"Initialized USER_EMOJIS with {len(records)} user emojis")

# Load leaderboard data
async def load_leaderboard(pool):
    async with get_db_connection(pool) as conn:
        try:
            rows = await conn.fetch("SELECT chat_id, user_id, name, score FROM leaderboard")
            data = {}
            for row in rows:
                chat_id = row["chat_id"]
                if chat_id not in data:
                    data[chat_id] = {"players": {}}
                data[chat_id]["players"][row["user_id"]] = {"name": row["name"], "score": row["score"]}
            return data
        except Exception as e:
            logger.error(f"Error loading leaderboard: {e}")
            return {}

# Load global leaderboard data
async def load_global_leaderboard(pool):
    async with get_db_connection(pool) as conn:
        try:
            users = {}
            rows = await conn.fetch("SELECT user_id, name, score FROM global_leaderboard")
            for row in rows:
                users[row["user_id"]] = {"name": row["name"], "score": row["score"], "groups": {}}
            
            rows = await conn.fetch("SELECT user_id, group_id, group_name, score FROM global_leaderboard_groups")
            for row in rows:
                users[row["user_id"]]["groups"][row["group_id"]] = {
                    "group_name": row["group_name"],
                    "score": row["score"]
                }
            return users
        except Exception as e:
            logger.error(f"Error loading global leaderboard: {e}")
            return {}

# Load streak data
async def load_streak_data(pool):
    async with get_db_connection(pool) as conn:
        try:
            rows = await conn.fetch("SELECT chat_id, user_id, name, streak FROM streaks")
            data = {}
            for row in rows:
                chat_id = row["chat_id"]
                if chat_id not in data:
                    data[chat_id] = {}
                data[chat_id][row["user_id"]] = {"name": row["name"], "streak": row["streak"]}
            return data
        except Exception as e:
            logger.error(f"Error loading streak data: {e}")
            return {}

async def load_user_languages(pool):
    async with get_db_connection(pool) as conn:
        try:
            rows = await conn.fetch("SELECT user_id, language FROM user_languages")
            return {row["user_id"]: row["language"] for row in rows}
        except Exception as e:
            logger.error(f"Error loading user languages: {e}")
            return {}

# Load achievements from JSON file
with open("achievements.json", "r") as file:
    ACHIEVEMENTS = json.load(file)

# Load achievements data
async def load_achievements_data(pool):
    """
    Loads user achievements data, including a persistently tracked set of participated groups.
    """
    async with get_db_connection(pool) as conn: # Assuming get_db_connection is defined as in your full script
        try:
            # Fetch core user stats
            stats_rows = await conn.fetch("""
                SELECT user_id, correct_answers, current_streak, highest_streak,
                       quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                       groups_participated, total_points
                FROM user_stats
            """)
            # Ensure user_id is consistently a string
            stats_dict = {str(row["user_id"]): dict(row) for row in stats_rows}

            # Fetch earned achievements
            achievements_rows = await conn.fetch("SELECT user_id, achievement_id FROM achievements")
            user_ach_map = defaultdict(list)
            for row in achievements_rows:
                user_ach_map[str(row["user_id"])].append(row["achievement_id"])

            # Fetch all unique (user_id, group_id) participations from global_leaderboard_groups
            # This table tracks every group a user has scored points in.
            participated_groups_rows = await conn.fetch(
                "SELECT DISTINCT user_id, group_id FROM global_leaderboard_groups"
            )
            user_participated_groups_map = defaultdict(set)
            for row in participated_groups_rows:
                # Ensure both user_id and group_id are strings for consistency
                user_participated_groups_map[str(row["user_id"])].add(str(row["group_id"]))

            loaded_achievements_data = {} # This will become the global achievements_data

            # Combine all user IDs from stats, achievements, and participated groups
            # to ensure all users with any relevant data are processed.
            all_user_ids = set(stats_dict.keys()) | set(user_ach_map.keys()) | set(user_participated_groups_map.keys())

            for user_id_str in all_user_ids:
                user_stats_from_db = stats_dict.get(user_id_str, {})
                
                # CRITICAL: Populate _achievement_tracked_groups from the persisted data
                tracked_groups_for_this_user = user_participated_groups_map.get(user_id_str, set())
                
                # Set 'groups_participated' count directly from the size of the loaded set of unique groups.
                # This ensures consistency and corrects any previous overcounting.
                correct_groups_participated_count = len(tracked_groups_for_this_user)

                loaded_achievements_data[user_id_str] = {
                    "correct_answers": user_stats_from_db.get("correct_answers", 0),
                    "current_streak": user_stats_from_db.get("current_streak", 0),
                    "highest_streak": user_stats_from_db.get("highest_streak", 0),
                    "quick_answers": user_stats_from_db.get("quick_answers", 0),
                    "taylor_answers": user_stats_from_db.get("taylor_answers", 0),
                    "lyrics_answers": user_stats_from_db.get("lyrics_answers", 0),
                    "incorrect_answers": user_stats_from_db.get("incorrect_answers", 0),
                    "groups_participated": correct_groups_participated_count, # Use count from the persisted set
                    "total_points": user_stats_from_db.get("total_points", 0),
                    "achievements": user_ach_map.get(user_id_str, []),
                    "_achievement_tracked_groups": tracked_groups_for_this_user # Store the populated set
                }
                
                # Optional: Log if the groups_participated value from user_stats table was different
                db_groups_participated = user_stats_from_db.get("groups_participated")
                if db_groups_participated is not None and db_groups_participated != correct_groups_participated_count:
                    logger.warning(
                        f"User {user_id_str}: Corrected groups_participated from DB value {db_groups_participated} "
                        f"to {correct_groups_participated_count} based on actual unique group participations."
                    )

            logger.info(f"Successfully loaded achievements_data for {len(loaded_achievements_data)} users. "
                        f"_achievement_tracked_groups and groups_participated are now synchronized with persistent data.")
            return loaded_achievements_data
        except Exception as e:
            logger.error(f"Error in load_achievements_data: {e}", exc_info=True)
            return {} # Return empty dict on error to prevent bot from crashing

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

async def save_user_languages(data, pool):
    async with get_db_connection(pool) as conn:
        try:
            await conn.execute("DELETE FROM user_languages")
            async with conn.transaction():
                for user_id, language in data.items():
                    await conn.execute("""
                        INSERT INTO user_languages (user_id, language)
                        VALUES ($1, $2)
                        ON CONFLICT (user_id) DO UPDATE SET language = EXCLUDED.language
                    """, user_id, language)
            logger.info("User languages saved to PostgreSQL.")
        except Exception as e:
            logger.error(f"Error saving user languages: {e}")

def get_emoji_for_user(user_id):
    user_id_str = str(user_id)  # Ensure consistent string conversion
    user_data = USER_EMOJIS.get(user_id_str)
    if user_data and "emoji" in user_data:
        return user_data["emoji"]
    return "👤"  # Default emoji

async def save_user_emoji(user_id: str, name: str, emoji: str, pool):
    global USER_EMOJIS
    user_id = str(user_id)  # Ensure user_id is a string
    timestamp = datetime.now().isoformat()
    try:
        async with get_db_connection(pool) as conn:
            await conn.execute("""
                INSERT INTO user_emojis (user_id, name, emoji, created_at)
                VALUES ($1, $2, $3, $4)
                ON CONFLICT (user_id) DO UPDATE SET
                    name = EXCLUDED.name,
                    emoji = EXCLUDED.emoji,
                    created_at = EXCLUDED.created_at
            """, user_id, name, emoji, timestamp)
        USER_EMOJIS[user_id] = {"name": name, "emoji": emoji, "created_at": timestamp}
        logger.debug(f"Saved emoji {emoji} for user {user_id}")
    except Exception as e:
        logger.error(f"Error saving user emoji: {e}")

async def get_total_users(pool):
    """Count unique users who have interacted with the bot."""
    try:
        async with get_db_connection(pool) as conn:
            result = await conn.fetchval("""
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
                ) AS combined
            """)
            total_users = result or 0
            logger.info(f"Calculated total users: {total_users}")
            return total_users
    except Exception as e:
        logger.error(f"Error getting total users: {e}")
        return 0

async def get_total_groups(pool):
    """Count total groups the bot is a member of, based on bot_groups."""
    try:
        async with get_db_connection(pool) as conn:
            result = await conn.fetchval("SELECT COUNT(*) as total_groups FROM bot_groups")
            total_groups = result or 0
            logger.info(f"Calculated total groups: {total_groups}")
            return total_groups
    except Exception as e:
        logger.error(f"Error getting total groups: {e}")
        return 0

async def can_bot_operate(chat_id: str, context: ContextTypes.DEFAULT_TYPE) -> tuple[bool, str]:
    """
    Check if the bot can operate in the group based on member count or exception list.
    Returns: (can_operate: bool, message: str)
    """
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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

async def set_bot_commands():
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/setMyCommands"

    private_commands = [
        {"command": "start", "description": "Start the Bot"}
    ]
    group_commands = [
        {"command": "leaderboard", "description": "View the leaderboard"},
        {"command": "settings", "description": "(ADMINS) Configure group settings"},
        {"command": "streak", "description": "View streaks data"},
        {"command": "profile", "description": "View your stats"},
        {"command": "reportquestion", "description": "Report an incorrect question"}
    ]
    specific_group_commands = [
        {"command": "leaderboard", "description": "View the leaderboard"},
        {"command": "settings", "description": "(ADMINS) Configure group settings"},
        {"command": "streak", "description": "View streaks data"},
        {"command": "profile", "description": "View your stats"},
        {"command": "reportquestion", "description": "Report an incorrect question"},
        {"command": "stats", "description": "(ADMINS) View bot statistics"}
    ]

    # Create SSL context with certifi's CA bundle
    ssl_context = ssl.create_default_context(cafile=certifi.where())
    connector = aiohttp.TCPConnector(ssl=ssl_context)

    async with aiohttp.ClientSession(connector=connector) as session:
        # Set commands for private chats
        private_payload = {
            "commands": private_commands,
            "scope": {"type": "all_private_chats"}
        }
        async with session.post(url, json=private_payload) as response:
            if response.status == 200:
                logger.info("Private chat commands set successfully!")
            else:
                logger.error(f"Failed to set private chat commands: {await response.text()}")

        # Set commands for all group chats
        group_payload = {
            "commands": group_commands,
            "scope": {"type": "all_group_chats"}
        }
        async with session.post(url, json=group_payload) as response:
            if response.status == 200:
                logger.info("Group chat commands set successfully!")
            else:
                logger.error(f"Failed to set group chat commands: {await response.text()}")

        # Set commands for the specific group
        specific_group_payload = {
            "commands": specific_group_commands,
            "scope": {
                "type": "chat",
                "chat_id": REPORT_GROUP_ID
            }
        }
        async with session.post(url, json=specific_group_payload) as response:
            if response.status == 200:
                logger.info(f"Commands set successfully for specific group {REPORT_GROUP_ID}!")
            else:
                logger.error(f"Failed to set commands for specific group {REPORT_GROUP_ID}: {await response.text()}")

def is_valid_url(url):
    return url.startswith("https://")

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

async def load_group_settings(pool):
    async with get_db_connection(pool) as conn:
        try:
            rows = await conn.fetch("SELECT chat_id, group_name, answer_mode, quiz_interval, language FROM group_settings")
            return {row["chat_id"]: dict(row) for row in rows}
        except Exception as e:
            logger.error(f"Error loading group settings: {e}")
            return {}

async def save_group_settings(data, pool):
    async with get_db_connection(pool) as conn:
        try:
            await conn.execute("DELETE FROM group_settings")
            async with conn.transaction():
                for chat_id, settings in data.items():
                    await conn.execute("""
                        INSERT INTO group_settings (chat_id, group_name, answer_mode, quiz_interval, language)
                        VALUES ($1, $2, $3, $4, $5)
                        ON CONFLICT (chat_id) DO UPDATE SET
                            group_name = EXCLUDED.group_name,
                            answer_mode = EXCLUDED.answer_mode,
                            quiz_interval = EXCLUDED.quiz_interval,
                            language = EXCLUDED.language
                    """, chat_id, settings["group_name"], settings["answer_mode"], settings["quiz_interval"], settings["language"])
            logger.info("Group settings saved to PostgreSQL.")
            return True
        except Exception as e:
            logger.error(f"Error saving group settings: {e}")
            return False

# Dictionary to track user activity
user_activity = defaultdict(dict)

# Rate limit settings (e.g., 1 command per 5 seconds)
RATE_LIMIT = 10  # Seconds between commands

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
                await save_user_emoji(user_id, first_name, emoji, context.bot_data["db_pool"])
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

async def save_achievements_data(data, pool):
    async with ACHIEVEMENTS_DATA_LOCK:
        try:
            async with get_db_connection(pool) as conn:
                async with conn.transaction():
                    for user_id, user_data in data.items():
                        await conn.execute("""
                            INSERT INTO user_stats (
                                user_id, correct_answers, current_streak, highest_streak,
                                quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                                groups_participated, total_points
                            )
                            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
                            ON CONFLICT (user_id) DO UPDATE SET
                                correct_answers = EXCLUDED.correct_answers,
                                current_streak = EXCLUDED.current_streak,
                                highest_streak = EXCLUDED.highest_streak,
                                quick_answers = EXCLUDED.quick_answers,
                                taylor_answers = EXCLUDED.taylor_answers,
                                lyrics_answers = EXCLUDED.lyrics_answers,
                                incorrect_answers = EXCLUDED.incorrect_answers,
                                groups_participated = EXCLUDED.groups_participated,
                                total_points = EXCLUDED.total_points
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
                        await conn.execute("DELETE FROM achievements WHERE user_id = $1", user_id)
                        # Insert current achievements
                        for ach_id in user_data["achievements"]:
                            await conn.execute("""
                                INSERT INTO achievements (user_id, achievement_id)
                                VALUES ($1, $2)
                                ON CONFLICT (user_id, achievement_id) DO NOTHING
                            """, user_id, ach_id)
            logger.info("Achievements data saved to PostgreSQL.")
        except Exception as e:
            logger.error(f"Error saving achievements data: {e}")

# Global Rank Calculation
async def get_global_rank(user_id, pool):
    global_leaderboard = await load_global_leaderboard(pool)
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

# Reset leaderboard
async def reset_leaderboard(chat_id, pool):
    global leaderboard_data
    chat_id_str = str(chat_id)
    leaderboard_data[chat_id_str] = {"players": {}}
    await save_leaderboard(leaderboard_data, pool)
    logger.info(f"Leaderboard reset for chat {chat_id_str}")
    return True

# Save leaderboard data
async def save_leaderboard(data, pool):
    async with pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute("DELETE FROM leaderboard")
            for chat_id, chat_data in data.items():
                for user_id, user_data in chat_data["players"].items():
                    await conn.execute("""
                        INSERT INTO leaderboard (chat_id, user_id, name, score)
                        VALUES ($1, $2, $3, $4)
                        ON CONFLICT (chat_id, user_id) DO UPDATE SET
                            name = EXCLUDED.name,
                            score = EXCLUDED.score
                    """, chat_id, user_id, user_data["name"], user_data["score"])
        logger.info("Leaderboard data saved to PostgreSQL.")
        return True

# Save streak data
async def save_streak_data(data, pool):
    async with pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute("DELETE FROM streaks")
            for chat_id, chat_data in data.items():
                for user_id, user_data in chat_data.items():
                    await conn.execute("""
                        INSERT INTO streaks (chat_id, user_id, name, streak)
                        VALUES ($1, $2, $3, $4)
                        ON CONFLICT (chat_id, user_id) DO UPDATE SET
                            name = EXCLUDED.name,
                            streak = EXCLUDED.streak
                    """, chat_id, user_id, user_data["name"], user_data["streak"])
        logger.info("Streak data saved to PostgreSQL.")
        return True

# Function to add a reaction using the Telegram Bot API
async def add_reaction_bot(chat_id, message_id, emoji="🎉", is_big=True):
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/setMessageReaction"
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reaction": [{"type": "emoji", "emoji": emoji, "is_big": is_big}]
    }
    # Create a ClientSession with SSL verification disabled
    async with aiohttp.ClientSession(connector=aiohttp.TCPConnector(ssl=False)) as session:
        async with session.post(url, json=payload) as response:
            if response.status == 200:
                logger.info(f"Reaction added as bot: {emoji} (Big: {is_big})")
            else:
                logger.error(f"Failed to add reaction: {await response.text()}")

# Start Command
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle the /start command, initialize user data, and send welcome message."""
    if update.message.chat.type != "private":
        return  # Ignore if not in private chat

    user_id = str(update.message.from_user.id)  # Ensure user_id is a string
    chat_id = update.message.chat_id
    bot_username = context.bot.username
    first_name = update.message.from_user.first_name  # Get user's first name (e.g., Hafeel)

    # Insert or update user language in the database
    async with context.bot_data["db_pool"].acquire() as conn:
        await conn.execute(
            "INSERT INTO user_languages (user_id, language) VALUES ($1, $2) ON CONFLICT (user_id) DO NOTHING",
            user_id, "en"
        )

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
        [InlineKeyboardButton(localized["support"], url="https://t.me/MastermindBotSupport"),
         InlineKeyboardButton(localized["updates"], url="https://t.me/MastermindBotUpdates")],
        [InlineKeyboardButton(localized["language"], callback_data="language_select"),
         InlineKeyboardButton(localized.get("emoji_select_button"), callback_data="emoji_select")],
         [InlineKeyboardButton(localized["add_to_group"], url=f"https://t.me/{bot_username}?startgroup=true")]
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

# Stats Command
async def stats_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Display bot statistics including working groups, no access groups, and banned groups."""
    user_id = str(update.message.from_user.id)
    chat_id = str(update.message.chat_id)
    chat_type = update.message.chat.type

    # Load group settings to get language
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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

    # Get statistics
    total_users = await get_total_users(context.bot_data["db_pool"])
    total_groups = await get_total_groups(context.bot_data["db_pool"])  # Uses bot_groups table
    working_groups = len(group_settings)  # Count all groups in group_settings
    
    # Get all groups the bot is in
    bot_groups = await get_bot_groups(context, context.bot_data["db_pool"])
    
    # No access groups: Bot is a member but no group_settings entry
    no_access_groups = len(bot_groups - set(group_settings.keys()))
    
    # Banned groups
    banned_groups_count = len(BANNED_GROUPS)

    # Format the response
    message = localized.get(
        "stats_message_extended",
        "📊 <b>Bot Statistics</b>\n\n"
        "👤 <b>Total Users</b>: {users}\n"
        "🏠 <b>Total Groups</b>: {total_groups}\n"
        "✅ <b>Working Groups</b>: {working_groups}\n"
        "🚫 <b>No Access Groups</b>: {no_access_groups}\n"
        "🔴 <b>Banned Groups</b>: {banned_groups}"
    ).format(
        users=total_users,
        total_groups=total_groups,
        working_groups=working_groups,
        no_access_groups=no_access_groups,
        banned_groups=banned_groups_count
    )

    try:
        await update.message.reply_text(message, parse_mode=ParseMode.HTML)
        logger.info(f"Sent stats to user {user_id} in chat {chat_id}: {total_users} users, {total_groups} total groups, "
                    f"{working_groups} working, {no_access_groups} no access, {banned_groups_count} banned")
    except Exception as e:
        logger.error(f"Failed to send stats to chat {chat_id}: {e}")
        await update.message.reply_text(localized["generic_error"], parse_mode=ParseMode.HTML)

# SEND QUESTION
async def prepare_questions_for_interval(context: ContextTypes.DEFAULT_TYPE):
    start_time = time.time()
    logger.info(f"Preparing questions for interval at {datetime.now(pytz.utc)} (epoch: {start_time})")

    interval = context.job.data.get("interval")
    if not interval:
        logger.error("No interval provided in job data")
        return

    interval_str = interval // 3600
    logger.info(f"Preparing questions for {interval_str}-hour interval")

    group_settings = await load_group_settings(context.bot_data["db_pool"])
    if not group_settings:
        logger.error("No group settings found")
        return

    target_groups = {
        chat_id: settings for chat_id, settings in group_settings.items()
        if settings.get("quiz_interval") == interval
    }
    if not target_groups:
        logger.warning(f"No groups found with quiz_interval {interval}")
        return

    logger.info(f"Preparing for {len(target_groups)} groups: {list(target_groups.keys())}")

    question_cache[interval] = {}
    bot_id = context.bot.id

    async def validate_image_path(file_path: str) -> bool:
        try:
            if not os.path.isfile(file_path):
                logger.error(f"Image file not found: {file_path}")
                return False
            with open(file_path, 'rb') as f:
                f.read(1)
            logger.info(f"Validated image file: {file_path}")
            return True
        except Exception as e:
            logger.error(f"Error validating image {file_path}: {e}")
            return False

    async def prepare_group(chat_id, settings):
        try:
            language = settings.get("language", "en")
            if language not in localization:
                logger.warning(f"Invalid language '{language}' for chat {chat_id}, falling back to 'en'")
                language = "en"
            localized = localization.get(language, localization["en"])
            logger.info(f"Using language '{language}' for chat {chat_id}")

            answer_mode = settings.get("answer_mode", "buttons")

            try:
                chat_member = await context.bot.get_chat_member(chat_id, bot_id)
                if chat_member.status not in [ChatMemberStatus.MEMBER, ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
                    logger.warning(f"Bot is not a member of chat {chat_id}")
                    return None
            except Exception as e:
                logger.error(f"Error checking bot membership for {chat_id}: {e}")
                return None

            can_operate, message = await can_bot_operate(chat_id, context)
            if not can_operate:
                logger.info(f"Cannot operate in {chat_id}: {message}")
                await context.bot.send_message(
                    chat_id=chat_id,
                    text=message,
                    parse_mode=ParseMode.HTML
                )
                return None

            available_types = []
            if lyrics_questions:
                available_types.append("lyrics")
            if taylor_questions:
                available_types.append("taylor")
            if not available_types:
                logger.error(f"No question types available for group {chat_id}")
                return None

            question_type = random.choice(available_types)
            question_pool = lyrics_questions if question_type == "lyrics" else taylor_questions
            if not question_pool:
                logger.error(f"Empty question pool for {question_type} in group {chat_id}")
                return None

            max_attempts = 10
            for attempt in range(max_attempts):
                question = random.choice(question_pool)
                question_number = question.get("questionnumber", "Unknown")
                correct_answers = question.get("answer", [])
                options = question.get("options", [])
                image_path = question.get("image")
                question_text = question.get("question")

                if not question_text:
                    logger.warning(f"Question {question_number} in {chat_id} has no question text")
                    continue
                if not correct_answers:
                    logger.warning(f"Question {question_number} in {chat_id} has no correct answers")
                    continue
                if not options:
                    logger.warning(f"Question {question_number} in {chat_id} has no options")
                    continue
                if not image_path:
                    logger.warning(f"Question {question_number} in {chat_id} has no image path")
                    continue

                if not await validate_image_path(image_path):
                    logger.warning(f"Invalid or missing image for question {question_number} in {chat_id}")
                    continue

                prompt_key = "lyrics_prompt" if question_type == "lyrics" else "taylor_prompt"
                if prompt_key not in localized:
                    logger.warning(f"Missing '{prompt_key}' in localization for language '{language}' in chat {chat_id}")
                    localized[prompt_key] = localization["en"].get(
                        prompt_key,
                        f"{question_type.capitalize()} Quiz: {question_text}"
                    )
                caption = localized[prompt_key]

                reply_markup = None
                effective_answer_mode = answer_mode  # Track the mode we'll actually use

                if answer_mode == "buttons" and options:
                    random.shuffle(options)
                    buttons = []
                    callback_too_long = False
                    for opt in options:
                        safe_opt = re.sub(r"[^\w\s]", "", opt.lower())[:57]
                        callback_data = f"answer_{safe_opt}"
                        if len(callback_data.encode("utf-8")) > 64:
                            logger.warning(f"Callback data too long: '{callback_data}' for {chat_id}. Switching to write mode.")
                            callback_too_long = True
                            break
                        buttons.append([InlineKeyboardButton(f"›› {opt}", callback_data=callback_data)])

                    if callback_too_long:
                        effective_answer_mode = "write"  # Switch to write mode
                        reply_markup = None  # No buttons
                        logger.info(f"Switched to write mode for chat {chat_id} due to long callback data.")
                    elif buttons:
                        reply_markup = InlineKeyboardMarkup(buttons)
                        logger.info(f"Created {len(buttons)} buttons for chat {chat_id}")
                    else:
                        logger.warning(f"No valid buttons for {chat_id}, falling back to write mode")
                        effective_answer_mode = "write"

                return {
                    "chat_id": chat_id,
                    "image": image_path,
                    "caption": caption,
                    "reply_markup": reply_markup,
                    "correct_answers": correct_answers,
                    "type": question_type,
                    "question_number": question_number,
                    "answer_mode": effective_answer_mode  # Use the effective mode
                }

            logger.error(f"No valid question found for {chat_id} after {max_attempts} attempts")
            return None

        except Exception as e:
            logger.error(f"Error preparing question for {chat_id}: {e}")
            return None

    tasks = [prepare_group(chat_id, settings) for chat_id, settings in target_groups.items()]
    results = await asyncio.gather(*tasks, return_exceptions=True)

    for chat_id, result in zip(target_groups.keys(), results):
        if isinstance(result, Exception):
            logger.error(f"Failed to prepare question for {chat_id}: {result}")
        elif result:
            question_cache[interval][chat_id] = result
            logger.info(f"Prepared question for {chat_id}: type={result['type']}, number={result['question_number']}")

    total_time = time.time() - start_time
    logger.info(f"Preparation completed in {total_time:.2f} seconds for {len(target_groups)} groups")
    logger.debug(f"question_cache[{interval}] contents: {list(question_cache[interval].keys())}")

async def send_questions_to_all_groups(context: ContextTypes.DEFAULT_TYPE):
    start_time_batch_send = time.time()
    logger.info(f"Sending questions at {datetime.now(pytz.utc)} (epoch: {start_time_batch_send})")

    interval = context.job.data.get("interval")
    if not interval:
        logger.error("No interval provided in job data for send_questions_to_all_groups")
        return

    if interval not in question_cache or not question_cache.get(interval):
        logger.error(f"No precomputed questions for interval {interval} in send_questions_to_all_groups. Cache for interval is missing or empty.")
        return

    if not question_cache[interval]:
        logger.warning(f"Precomputed question cache for interval {interval} is empty. No questions to send.")
        return

    metrics = {
        "successful_sends": 0,
        "failed_sends": 0,
        "send_photo_times": [],
        "rate_limiter_times": [],
        "storage_times": [],
        "job_schedule_times": []
    }

    async def load_local_image(file_path: str) -> io.BytesIO:
        try:
            with open(file_path, 'rb') as f:
                image_data = io.BytesIO(f.read())
            return image_data
        except FileNotFoundError:
            logger.error(f"Image file not found during load_local_image: {file_path}")
            return None
        except Exception as e:
            logger.error(f"Error loading image {file_path}: {e}")
            return None

    async def send_to_group(chat_id_internal, question_data_internal):
        chat_lock = CHAT_SEND_LOCKS[chat_id_internal]
        if chat_lock.locked():
            logger.warning(f"Chat {chat_id_internal} is already locked for sending by another task. Skipping this redundant attempt.")
            raise Exception(f"Skipped sending to chat {chat_id_internal}: Lock already held.")

        async with chat_lock:
            logger.info(f"Acquired send lock for chat {chat_id_internal} for question number {question_data_internal.get('question_number')}")
            photo_message_obj = None
            photo_sent_successfully = False
            max_photo_send_attempts = 10
            photo_send_delay = 3

            try:
                image_path_internal = question_data_internal.get("image")
                if not image_path_internal:
                    logger.error(f"No image path for {chat_id_internal} in question_data.")
                    raise ValueError(f"Missing image path for chat {chat_id_internal}")

                logger.info(f"Attempting send for chat {chat_id_internal} (Q#: {question_data_internal.get('question_number')}). Loading image: {image_path_internal}")

                for attempt in range(max_photo_send_attempts):
                    image_data_internal = None
                    try:
                        if attempt > 0:
                            logger.info(f"Retrying send for chat {chat_id_internal} (Q#: {question_data_internal.get('question_number')}), attempt {attempt + 1}. Reloading image.")

                        image_data_internal = await load_local_image(image_path_internal)
                        if not image_data_internal:
                            logger.error(f"Failed to load image {image_path_internal} for {chat_id_internal} on attempt {attempt + 1}.")
                            if attempt == max_photo_send_attempts - 1:
                                raise IOError(f"Failed to load image after {max_photo_send_attempts} attempts for {chat_id_internal}")
                            await asyncio.sleep(photo_send_delay)
                            continue

                        logger.info(f"Loaded {image_path_internal} for attempt {attempt + 1}, size={len(image_data_internal.getvalue())} bytes for chat {chat_id_internal}")

                        limiter_start_internal = time.time()
                        async with SEND_RATE_LIMITER:
                            limiter_time_internal = time.time() - limiter_start_internal
                            metrics["rate_limiter_times"].append(limiter_time_internal)

                            api_start_internal = time.time()
                            photo_message_obj = await context.bot.send_photo(
                                chat_id=chat_id_internal,
                                photo=image_data_internal,
                                caption=question_data_internal["caption"],
                                parse_mode="HTML",
                                reply_markup=question_data_internal["reply_markup"],
                                protect_content=True,
                                has_spoiler=True,
                                read_timeout=15,
                                write_timeout=15,
                                connect_timeout=10
                            )
                            api_time_internal = time.time() - api_start_internal
                            metrics["send_photo_times"].append(api_time_internal)
                            photo_sent_successfully = True
                            break

                    except telegram.error.TimedOut as e_timeout:
                        logger.warning(f"Attempt {attempt + 1}/{max_photo_send_attempts} to send photo to {chat_id_internal} (Q#: {question_data_internal.get('question_number')}) timed out: {e_timeout}")
                        if attempt == max_photo_send_attempts - 1:
                            logger.error(f"All {max_photo_send_attempts} attempts to send photo to {chat_id_internal} (Q#: {question_data_internal.get('question_number')}) failed (TimedOut).")
                            raise
                        await asyncio.sleep(photo_send_delay)
                    except Exception as e_general:
                        logger.error(f"Attempt {attempt + 1}/{max_photo_send_attempts} to send photo to {chat_id_internal} (Q#: {question_data_internal.get('question_number')}) failed: {e_general}")
                        raise
                    finally:
                        if image_data_internal:
                            image_data_internal.close()

                if not photo_sent_successfully or not photo_message_obj:
                    logger.error(f"Photo send loop for {chat_id_internal} (Q#: {question_data_internal.get('question_number')}) completed without confirmed success or propagated exception.")
                    raise Exception(f"Photo send ultimately failed for {chat_id_internal} (Q#: {question_data_internal.get('question_number')}) after all retries.")

                metrics["successful_sends"] += 1
                logger.info(f"QUESTION SENT (final status): chat_id={chat_id_internal}, type={question_data_internal['type']}, number={question_data_internal['question_number']}, msg_id={photo_message_obj.message_id}, answer_mode={question_data_internal['answer_mode']}")

                storage_start_internal = time.time()
                question_key_internal = f"{chat_id_internal}_{photo_message_obj.message_id}"
                active_questions[question_key_internal] = {
                    "chat_id": chat_id_internal,
                    "correct_answers": question_data_internal["correct_answers"],
                    "start_time": time.time(),
                    "type": question_data_internal["type"],
                    "answered": False,
                    "message_id": photo_message_obj.message_id,
                    "question_number": question_data_internal["question_number"],
                    "answer_mode": question_data_internal["answer_mode"]  # Store the effective answer mode
                }
                storage_time_internal = time.time() - storage_start_internal
                metrics["storage_times"].append(storage_time_internal)
                logger.debug(f"Stored active_questions for {chat_id_internal} (key: {question_key_internal}) in {storage_time_internal:.3f}s")

                job_start_internal = time.time()
                context.job_queue.run_once(
                    send_alarm,
                    300,
                    chat_id=chat_id_internal,
                    name=f"alarm_{question_key_internal}",
                    data={"question_key": question_key_internal}
                )
                context.job_queue.run_once(
                    update_caption,
                    600,
                    chat_id=chat_id_internal,
                    name=f"timeup_{question_key_internal}",
                    data={"question_key": question_key_internal}
                )
                job_time_internal = time.time() - job_start_internal
                metrics["job_schedule_times"].append(job_time_internal)
                logger.debug(f"Scheduled jobs for {chat_id_internal} (key: {question_key_internal}) in {job_time_internal:.3f}s")

            except Exception as e_outer_sg:
                logger.error(f"Overall error during send_to_group for {chat_id_internal} (Q#: {question_data_internal.get('question_number')}): {e_outer_sg}")
                raise
            finally:
                logger.info(f"Released send lock for chat {chat_id_internal} for question number {question_data_internal.get('question_number')}")
    tasks = []
    processed_chat_ids_for_this_job_run = set()
    current_interval_cache = question_cache.get(interval)
    if current_interval_cache:
        for chat_id_task, question_data_task in current_interval_cache.items():
            if chat_id_task not in processed_chat_ids_for_this_job_run:
                tasks.append(send_to_group(chat_id_task, question_data_task))
                processed_chat_ids_for_this_job_run.add(chat_id_task)
            else:
                logger.warning(f"Duplicate chat_id {chat_id_task} encountered in question_cache for interval {interval}. Skipping redundant task creation.")
    else:
        logger.error(f"Question cache for interval {interval} was unexpectedly missing or became empty before task creation.")

    if not tasks:
        logger.warning(f"No tasks created for sending questions for interval {interval}. Cache might be empty or all groups skipped due to locks.")

    send_start_gather = time.time()
    results = await asyncio.gather(*tasks, return_exceptions=True)
    send_time_gather = time.time() - send_start_gather
    logger.debug(f"asyncio.gather for {len(tasks)} groups took {send_time_gather:.3f}s")
    chat_ids_for_results = list(processed_chat_ids_for_this_job_run)

    for i, result_item in enumerate(results):
        if i < len(chat_ids_for_results):
            original_chat_id = chat_ids_for_results[i]
            if isinstance(result_item, Exception):
                if "Skipped sending" in str(result_item) and "Lock already held" in str(result_item):
                    logger.warning(f"Send task for {original_chat_id} was deliberately skipped due to lock: {result_item}")
                else:
                    logger.error(f"send_to_group task for {original_chat_id} definitively failed with: {result_item}")
                    metrics["failed_sends"] += 1
            else:
                logger.info(f"send_to_group task for {original_chat_id} completed (presumed success as no exception, details logged within).")
        else:
            logger.error(f"Result item at index {i} without a corresponding chat_id for logging. Result: {result_item}")

    total_time_batch_send = time.time() - start_time_batch_send
    avg_photo_time = sum(metrics["send_photo_times"]) / len(metrics["send_photo_times"]) if metrics["send_photo_times"] else 0
    max_photo_time = max(metrics["send_photo_times"], default=0)
    total_limiter_time = sum(metrics["rate_limiter_times"])
    total_storage_time = sum(metrics["storage_times"])
    total_job_time = sum(metrics["job_schedule_times"])

    logger.info(
        f"Sending summary: "
        f"successful_sends_metric={metrics['successful_sends']}, "
        f"failed_sends_metric={metrics['failed_sends']}, "
        f"avg_photo_time={avg_photo_time:.3f}s, "
        f"max_photo_time={max_photo_time:.3f}s, "
        f"total_limiter_time={total_limiter_time:.3f}s, "
        f"total_storage_time={total_storage_time:.3f}s, "
        f"total_job_time={total_job_time:.3f}s, "
        f"total_batch_send_time={total_time_batch_send:.3f}s"
    )

    if interval in question_cache:
        question_cache.pop(interval, None)
        logger.debug(f"Cleaned up question_cache[{interval}]")

    logger.info(f"Sending completed in {total_time_batch_send:.2f} seconds for {len(tasks)} groups initially targeted for sending.")

# Schedule Quiz Jobs
async def schedule_quiz_jobs(job_queue, chat_id: str, interval: int, pool):
    """Schedule preparation and sending jobs for quiz intervals."""
    chat_id = str(chat_id)
    group_settings = await load_group_settings(pool)
    group_settings[chat_id]["quiz_interval"] = interval
    await save_group_settings(group_settings, pool)
    logger.info(f"Updated quiz interval for chat {chat_id} to {interval}s")

    supported_intervals = [3600, 7200, 10800, 14400, 21600, 28800, 43200, 86400]
    async with GLOBAL_SCHEDULING_LOCK:
        for interval_seconds in supported_intervals:
            job_name = f"batch_send_{interval_seconds}"
            prep_job_name = f"prepare_{interval_seconds}"
            existing_jobs = job_queue.get_jobs_by_name(job_name)
            existing_prep_jobs = job_queue.get_jobs_by_name(prep_job_name)

            if not existing_jobs:
                delay = get_next_interval_time(interval_seconds)
                asyncio.create_task(start_repeating_job(job_queue, interval_seconds, delay, job_name, prep_job_name))
                logger.info(f"Scheduled initial tasks for {job_name} and {prep_job_name} with first run in {delay}s")

async def start_repeating_job(job_queue, interval_seconds, delay, job_name, prep_job_name):
    """Start preparation and sending jobs at the precise time."""
    await asyncio.sleep(delay - 60)  # Start preparation 60 seconds earlier
    job_queue.run_repeating(
        prepare_questions_for_interval,
        interval=interval_seconds,
        name=prep_job_name,
        data={"interval": interval_seconds}
    )
    logger.info(f"Started repeating preparation job {prep_job_name} with interval {interval_seconds}s")

    await asyncio.sleep(60)  # Wait until the exact interval time
    job_queue.run_repeating(
        send_questions_to_all_groups,
        interval=interval_seconds,
        name=job_name,
        data={"interval": interval_seconds}
    )
    logger.info(f"Started repeating sending job {job_name} with interval {interval_seconds}s")

# ALARM SYSTEM
async def send_alarm(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    question_key = job.data["question_key"]

    if question_key in active_questions:
        question_data = active_questions[question_key]
        if not question_data["answered"]:
            group_settings = await load_group_settings(context.bot_data["db_pool"])
            group_language = group_settings.get(str(chat_id), {}).get("language", "en")
            localized = localization.get(group_language, localization["en"])

            try:
                message = await context.bot.send_message(
                    chat_id=chat_id,
                    text=localized["alarm"],
                    reply_to_message_id=question_data["message_id"],
                    disable_notification=True  # AVOID EXCESSIVE NOTIFICATIONS
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

    group_settings = await load_group_settings(context.bot_data["db_pool"])
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

# Log active jobs        
async def log_active_jobs(job_queue):
    while True:
        try:
            jobs = job_queue.jobs()
            logger.info(f"Active jobs: {len(jobs)}")
            for job in jobs:
                logger.info(f"Job {job.name} scheduled")
        except Exception as e:
            logger.error(f"Error in log_active_jobs: {str(e)}")
        await asyncio.sleep(3600)

# DELETE MESSAGE FUNCTION
async def delete_message(context: ContextTypes.DEFAULT_TYPE):
    job = context.job
    chat_id = job.chat_id
    message_id = job.data["message_id"]

    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception as e:
        logger.error(f"Failed to delete message: {e}")

# HANDLE ANSWER AND UPDATE GLOBAL LEADERBOARD BUTTONS
async def handle_answer(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle button-based quiz answers with immediate feedback, 5-second timeout for incorrect answers, and deferred DB updates."""
    query = update.callback_query
    data = query.data
    if not data.startswith("answer_"):
        await query.answer("❌ Invalid input.")
        return
    chat_id = str(query.message.chat_id)
    user_id = str(query.from_user.id)
    user_name = sanitize_input(query.from_user.first_name or "Unknown")
    selected_answer = data.replace("answer_", "")  # Extract answer from callback data
    question_key = f"{chat_id}_{query.message.message_id}"
    message_id = query.message.message_id

    # Load group settings and localization
    group_settings = await load_group_settings(context.bot_data["db_pool"])
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    # Check if question is still active
    if question_key not in active_questions:
        await query.answer(localized.get("question_expired", "⏳ Time's up! No more answers accepted."), show_alert=True)
        return

    question_data = active_questions[question_key]
    correct_answers = question_data["correct_answers"]
    start_time = question_data["start_time"]
    elapsed_time = time.time() - start_time
    question_type = question_data["type"]

    # Direct comparison for button mode (no normalization needed)
    is_correct = selected_answer in correct_answers

    # Handle emoji assignment
    current_emoji = USER_EMOJIS.get(user_id, {}).get("emoji", None)
    current_name = USER_EMOJIS.get(user_id, {}).get("name", None)
    if current_emoji is None:
        async with context.bot_data["db_pool"].acquire() as conn:
            record = await conn.fetchrow(
                "SELECT emoji, name, created_at FROM user_emojis WHERE user_id = $1",
                user_id
            )
            if record:
                current_emoji = record["emoji"]
                USER_EMOJIS[user_id] = {
                    "name": record["name"],
                    "emoji": current_emoji,
                    "created_at": record["created_at"]
                }
                logger.info(f"Loaded emoji {current_emoji} for user {user_id} from database")
            else:
                current_emoji = "👤"
                created_at = datetime.now(timezone.utc).isoformat()
                USER_EMOJIS[user_id] = {
                    "name": user_name,
                    "emoji": current_emoji,
                    "created_at": created_at
                }
                DB_WRITE_QUEUE.put_nowait((
                    """
                    INSERT INTO user_emojis (user_id, name, emoji, created_at)
                    VALUES ($1, $2, $3, $4)
                    ON CONFLICT (user_id) DO UPDATE SET
                        name = $2,
                        emoji = $3,
                        created_at = $4
                    """,
                    (user_id, user_name, current_emoji, created_at)
                ))
                logger.info(f"Queued default emoji {current_emoji} for user {user_id} with created_at {created_at}")
    elif current_name != user_name:
        created_at = USER_EMOJIS[user_id].get("created_at", datetime.now(timezone.utc).isoformat())
        USER_EMOJIS[user_id]["name"] = user_name
        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO user_emojis (user_id, name, emoji, created_at)
            VALUES ($1, $2, $3, $4)
            ON CONFLICT (user_id) DO UPDATE SET
                name = $2,
                emoji = $3,
                created_at = $4
            """,
            (user_id, user_name, current_emoji, created_at)
        ))
        logger.info(f"Queued name update for user {user_id} with emoji {current_emoji}")

    if is_correct:
        # Clear any existing timeout for this user
        if f"timeout_end_{user_id}" in question_data:
            del question_data[f"timeout_end_{user_id}"]
            logger.debug(f"Cleared timeout for user {user_id} on correct answer")

        await process_correct_answer(
            update=update,
            chat_id=chat_id,
            user_id=user_id,
            user_name=user_name,
            selected_answer=selected_answer,
            formatted_time=elapsed_time,
            question_type=question_type,
            reply_message_id=message_id,
            context=context,
            question_key=question_key
        )
    else:
        # Check for timeout only for incorrect answers
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

        # Set timeout for incorrect answer
        timeout_duration = 5
        timeout_end_time = current_time + timeout_duration
        question_data[f"timeout_end_{user_id}"] = timeout_end_time

        await query.answer(
            localized["wrong_answer"].format(user_name=user_name) + "\n\n" +
            localized["timeout_initial"].format(timeout_duration=timeout_duration),
            show_alert=True
        )

        # Queue streak reset
        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO streaks (chat_id, user_id, name, streak)
            VALUES ($1, $2, $3, 0)
            ON CONFLICT (chat_id, user_id) DO UPDATE SET
                streak = 0,
                name = $3
            """,
            (chat_id, user_id, user_name)
        ))

        # Update and queue achievements
        achievements_data.setdefault(user_id, {
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
        })
        achievements_data[user_id]["incorrect_answers"] += 1
        achievements_data[user_id]["current_streak"] = 0

        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO user_stats (
                user_id, correct_answers, current_streak, highest_streak,
                quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                groups_participated, total_points
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
            ON CONFLICT (user_id) DO UPDATE SET
                correct_answers = $2,
                current_streak = $3,
                highest_streak = $4,
                quick_answers = $5,
                taylor_answers = $6,
                lyrics_answers = $7,
                incorrect_answers = $8,
                groups_participated = $9,
                total_points = $10
            """,
            (
                user_id,
                achievements_data[user_id]["correct_answers"],
                achievements_data[user_id]["current_streak"],
                achievements_data[user_id]["highest_streak"],
                achievements_data[user_id]["quick_answers"],
                achievements_data[user_id]["taylor_answers"],
                achievements_data[user_id]["lyrics_answers"],
                achievements_data[user_id]["incorrect_answers"],
                achievements_data[user_id]["groups_participated"],
                achievements_data[user_id]["total_points"]
            )
        ))

        # Schedule button re-enabling
        context.job_queue.run_once(
            reenable_buttons,
            timeout_duration,
            chat_id=chat_id,
            name=f"timeout_{question_key}",
            data={"message_id": message_id, "question_key": question_key, "selected_answer": selected_answer}
        )

    await query.answer()

# RE-ENABLE BUTTONS
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    global streak_data, achievements_data, active_questions, USER_EMOJIS, RANDOM_EMOJIS, client
    chat_id = str(update.message.chat_id)
    user_id = str(update.message.from_user.id)
    user_name = sanitize_input(update.message.from_user.first_name or "Unknown")
    raw_answer = update.message.text.strip()
    selected_answer = sanitize_input(raw_answer)
    replied_to = update.message.reply_to_message

    group_settings = await load_group_settings(context.bot_data["db_pool"])
    group_language = group_settings.get(chat_id, {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    question_key = None
    if replied_to:
        question_key = f"{chat_id}_{replied_to.message_id}"
        if question_key not in active_questions:
            return
    else:
        recent_question_key = None
        latest_start_time = 0
        for key, data_val in active_questions.items():
            if str(data_val["chat_id"]) == chat_id and not data_val["answered"]:
                if data_val["start_time"] > latest_start_time:
                    latest_start_time = data_val["start_time"]
                    recent_question_key = key
        question_key = recent_question_key
        if not question_key:
            return

    question_data = active_questions[question_key]
    question_answer_mode = question_data.get("answer_mode", "buttons")  # Get question-specific answer mode
    if question_answer_mode != "write":
        logger.debug(f"Ignoring text answer for question {question_key} in chat {chat_id} with question answer mode {question_answer_mode}")
        return

    correct_answers = question_data["correct_answers"]
    start_time = question_data["start_time"]
    elapsed_time = time.time() - start_time
    question_type = question_data["type"]

    def normalize_answer(text):
        if not text:
            return ""
        text = text.lower()
        text = text.replace('(', '').replace(')', '').replace("'", "")
        return text.strip()

    normalized_answer = normalize_answer(selected_answer)
    normalized_correct = [norm_ans for ans in correct_answers if ans and (norm_ans := normalize_answer(ans))]
    is_correct = normalized_answer and normalized_answer in normalized_correct

    current_emoji = USER_EMOJIS.get(user_id, {}).get("emoji", None)
    current_name = USER_EMOJIS.get(user_id, {}).get("name", None)
    if current_emoji is None:
        async with context.bot_data["db_pool"].acquire() as conn:
            record = await conn.fetchrow(
                "SELECT emoji, name, created_at FROM user_emojis WHERE user_id = $1",
                user_id
            )
            if record:
                current_emoji = record["emoji"]
                USER_EMOJIS[user_id] = {
                    "name": record["name"],
                    "emoji": current_emoji,
                    "created_at": record["created_at"]
                }
                logger.info(f"Loaded emoji {current_emoji} for user {user_id} from database")
            else:
                current_emoji = "👤"
                created_at = datetime.now(timezone.utc).isoformat()
                USER_EMOJIS[user_id] = {
                    "name": user_name,
                    "emoji": current_emoji,
                    "created_at": created_at
                }
                DB_WRITE_QUEUE.put_nowait((
                    """
                    INSERT INTO user_emojis (user_id, name, emoji, created_at)
                    VALUES ($1, $2, $3, $4)
                    ON CONFLICT (user_id) DO UPDATE SET
                        name = $2,
                        emoji = $3,
                        created_at = $4
                    """,
                    (user_id, user_name, current_emoji, created_at)
                ))
                logger.info(f"Queued default emoji {current_emoji} for user {user_id} with created_at {created_at}")
    elif current_name != user_name:
        created_at = USER_EMOJIS[user_id].get("created_at", datetime.now(timezone.utc).isoformat())
        USER_EMOJIS[user_id]["name"] = user_name
        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO user_emojis (user_id, name, emoji, created_at)
            VALUES ($1, $2, $3, $4)
            ON CONFLICT (user_id) DO UPDATE SET
                name = $2,
                emoji = $3,
                created_at = $4
            """,
            (user_id, user_name, current_emoji, created_at)
        ))
        logger.info(f"Queued name update for user {user_id} with emoji {current_emoji}")

    logger.info(f"User answer (text): '{selected_answer}' | Correct answers: {correct_answers} | "
                f"Normalized user answer: '{normalized_answer}' | "
                f"Normalized correct answers: {normalized_correct} | "
                f"Raw input: '{raw_answer}' | Question key: {question_key} | Answer mode: {question_answer_mode}")

    if is_correct:
        logger.info(f"Correct text answer detected for question {question_key} in chat {chat_id}")
        await process_correct_answer(
            update=update,
            chat_id=chat_id,
            user_id=user_id,
            user_name=user_name,
            selected_answer=selected_answer,
            formatted_time=elapsed_time,
            question_type=question_type,
            reply_message_id=update.message.message_id,
            context=context,
            question_key=question_key
        )
        random_emoji_reaction = random.choice(RANDOM_EMOJIS)
        try:
            await client(SendReactionRequest(
                peer=int(chat_id),
                big=True,
                msg_id=update.message.message_id,
                reaction=[ReactionEmoji(emoticon=random_emoji_reaction)],
            ))
            logger.info(f"Sent BIG emoji reaction (via Telethon) {random_emoji_reaction} in chat {chat_id} for text answer")
        except Exception as e:
            logger.error(f"Failed to send reaction (via Telethon) for text answer: {e}")

        if elapsed_time < 300:
            for job in context.job_queue.get_jobs_by_name(f"alarm_{question_key}"):
                job.schedule_removal()
                logger.info(f"Removed alarm job for question {question_key} due to correct text answer.")
    else:
        if user_id not in achievements_data:
            achievements_data[user_id] = {
                "correct_answers": 0, "current_streak": 0, "highest_streak": 0,
                "quick_answers": 0, "taylor_answers": 0, "lyrics_answers": 0,
                "incorrect_answers": 0, "groups_participated": 0, "total_points": 0,
                "achievements": [], "_achievement_tracked_groups": set()
            }
        elif "_achievement_tracked_groups" not in achievements_data[user_id]:
            achievements_data[user_id]["_achievement_tracked_groups"] = set()

        achievements_data[user_id]["incorrect_answers"] += 1
        achievements_data[user_id]["current_streak"] = 0

        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO streaks (chat_id, user_id, name, streak)
            VALUES ($1, $2, $3, 0)
            ON CONFLICT (chat_id, user_id) DO UPDATE SET
                streak = 0,
                name = $3
            """,
            (chat_id, user_id, user_name)
        ))

        DB_WRITE_QUEUE.put_nowait((
            """
            INSERT INTO user_stats (
                user_id, correct_answers, current_streak, highest_streak,
                quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
                groups_participated, total_points
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
            ON CONFLICT (user_id) DO UPDATE SET
                correct_answers = $2,
                current_streak = $3,
                highest_streak = $4,
                quick_answers = $5,
                taylor_answers = $6,
                lyrics_answers = $7,
                incorrect_answers = $8,
                groups_participated = $9,
                total_points = $10
            """,
            (
                user_id,
                achievements_data[user_id]["correct_answers"],
                achievements_data[user_id]["current_streak"],
                achievements_data[user_id]["highest_streak"],
                achievements_data[user_id]["quick_answers"],
                achievements_data[user_id]["taylor_answers"],
                achievements_data[user_id]["lyrics_answers"],
                achievements_data[user_id]["incorrect_answers"],
                achievements_data[user_id]["groups_participated"],
                achievements_data[user_id]["total_points"]
            )
        ))
        logger.info(f"Incorrect text answer by {user_id} for question {question_key}. Stats updated.")

async def process_correct_answer(update: Update, chat_id: str, user_id: str, user_name: str, selected_answer: str, formatted_time: float, question_type: str, reply_message_id: int, context: ContextTypes.DEFAULT_TYPE, question_key: str):
    elapsed_time_seconds = formatted_time

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

    group_settings = await load_group_settings(context.bot_data["db_pool"])
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization.get("en", {}))

    # Use question-specific answer_mode from active_questions
    question_answer_mode = active_questions.get(question_key, {}).get("answer_mode", "buttons")

    minutes = int(elapsed_time_seconds // 60)
    seconds = int(elapsed_time_seconds % 60)
    minute_key = "minutes" if minutes != 1 else "minute"
    second_key = "seconds" if seconds != 1 else "second"

    loc_minute_str = localized.get(minute_key, minute_key)
    loc_second_str = localized.get(second_key, second_key)

    formatted_time_str = f"{minutes} {loc_minute_str} {seconds} {loc_second_str}" if minutes > 0 else f"{seconds} {loc_second_str}"

    if question_type == "lyrics":
        response_key = "correct_lyrics_buttons" if question_answer_mode == "buttons" else "correct_lyrics_write"
    else:  # taylor
        response_key = "correct_taylor_buttons" if question_answer_mode == "buttons" else "correct_taylor_write"

    response_text_template = localized.get(response_key, "Correct! User: {name}, Time: {formatted_time}, Points: {points}")
    response_text = response_text_template.format(
        user_id=user_id,
        name=user_name,
        formatted_time=formatted_time_str,
        points=points
    )

    try:
        await context.bot.send_message(
            chat_id=chat_id,
            text=response_text,
            parse_mode="HTML",
            reply_to_message_id=reply_message_id
        )
        logger.info(f"Sent correct answer message for user {user_id} in chat {chat_id} with answer mode {question_answer_mode}")
    except Exception as e:
        logger.error(f"Failed to send correct answer message for user {user_id} in chat {chat_id}: {e}")

    question_message_id = active_questions.get(question_key, {}).get("message_id")
    if question_message_id:
        try:
            caption_key_template = "answered_lyrics" if question_type == "lyrics" else "answered_taylor"
            caption_text = localized.get(caption_key_template, "Question Answered!")
            await context.bot.edit_message_caption(
                chat_id=chat_id,
                message_id=question_message_id,
                caption=caption_text,
                parse_mode="HTML",
                reply_markup=None
            )
            logger.info(f"Updated caption for question {question_key}")
        except Exception as e:
            logger.error(f"Failed to update caption for question {question_key}: {e}")

    group_name = update.effective_chat.title if update.effective_chat else "Unknown"

    DB_WRITE_QUEUE.put_nowait((
        """
        INSERT INTO leaderboard (chat_id, user_id, name, score)
        VALUES ($1, $2, $3, $4)
        ON CONFLICT (chat_id, user_id) DO UPDATE SET
            score = leaderboard.score + $4,
            name = $3
        """,
        (str(chat_id), str(user_id), user_name, points)
    ))

    DB_WRITE_QUEUE.put_nowait((
        """
        INSERT INTO global_leaderboard (user_id, name, score)
        VALUES ($1, $2, $3)
        ON CONFLICT (user_id) DO UPDATE SET
            score = global_leaderboard.score + $3,
            name = $2
        """,
        (str(user_id), user_name, points)
    ))

    DB_WRITE_QUEUE.put_nowait((
        """
        INSERT INTO global_leaderboard_groups (user_id, group_id, group_name, score)
        VALUES ($1, $2, $3, $4)
        ON CONFLICT (user_id, group_id) DO UPDATE SET
            score = global_leaderboard_groups.score + $4,
            group_name = $3
        """,
        (str(user_id), str(chat_id), group_name, points)
    ))

    DB_WRITE_QUEUE.put_nowait((
        """
        INSERT INTO streaks (chat_id, user_id, name, streak)
        VALUES ($1, $2, $3, 1)
        ON CONFLICT (chat_id, user_id) DO UPDATE SET
            streak = streaks.streak + 1,
            name = $3
        """,
        (str(chat_id), str(user_id), user_name)
    ))

    if user_id not in achievements_data:
        achievements_data[user_id] = {
            "correct_answers": 0, "current_streak": 0, "highest_streak": 0,
            "quick_answers": 0, "taylor_answers": 0, "lyrics_answers": 0,
            "incorrect_answers": 0, "groups_participated": 0, "total_points": 0,
            "achievements": [], "_achievement_tracked_groups": set()
        }
    elif "_achievement_tracked_groups" not in achievements_data[user_id]:
        achievements_data[user_id]["_achievement_tracked_groups"] = set()
    if "groups_participated" not in achievements_data[user_id]:
        achievements_data[user_id]["groups_participated"] = len(achievements_data[user_id].get("_achievement_tracked_groups", set()))

    achievements_data[user_id]["correct_answers"] += 1
    achievements_data[user_id]["current_streak"] += 1
    achievements_data[user_id]["total_points"] += points
    if question_type == "taylor":
        achievements_data[user_id]["taylor_answers"] += 1
    elif question_type == "lyrics":
        achievements_data[user_id]["lyrics_answers"] += 1
    if elapsed_time_seconds <= 10:
        achievements_data[user_id]["quick_answers"] += 1
    if achievements_data[user_id]["current_streak"] > achievements_data[user_id]["highest_streak"]:
        achievements_data[user_id]["highest_streak"] = achievements_data[user_id]["current_streak"]

    current_chat_id_str = str(chat_id)
    if "_achievement_tracked_groups" not in achievements_data[user_id]:
        achievements_data[user_id]["_achievement_tracked_groups"] = set()
        if "groups_participated" not in achievements_data[user_id]:
            achievements_data[user_id]["groups_participated"] = 0

    if current_chat_id_str not in achievements_data[user_id]["_achievement_tracked_groups"]:
        achievements_data[user_id]["_achievement_tracked_groups"].add(current_chat_id_str)
        achievements_data[user_id]["groups_participated"] += 1
        logger.info(f"User {user_id} achievements: new group {current_chat_id_str} recorded. "
                    f"Total unique groups participated: {achievements_data[user_id]['groups_participated']}. "
                    f"Tracked set size: {len(achievements_data[user_id]['_achievement_tracked_groups'])}")
    else:
        if achievements_data[user_id]["groups_participated"] != len(achievements_data[user_id]["_achievement_tracked_groups"]):
            logger.warning(f"User {user_id}: Resyncing groups_participated ({achievements_data[user_id]['groups_participated']}) "
                           f"to tracked set size ({len(achievements_data[user_id]['_achievement_tracked_groups'])}).")
            achievements_data[user_id]["groups_participated"] = len(achievements_data[user_id]["_achievement_tracked_groups"])

    DB_WRITE_QUEUE.put_nowait((
        """
        INSERT INTO user_stats (
            user_id, correct_answers, current_streak, highest_streak,
            quick_answers, taylor_answers, lyrics_answers, incorrect_answers,
            groups_participated, total_points
        )
        VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
        ON CONFLICT (user_id) DO UPDATE SET
            correct_answers = EXCLUDED.correct_answers,
            current_streak = EXCLUDED.current_streak,
            highest_streak = EXCLUDED.highest_streak,
            quick_answers = EXCLUDED.quick_answers,
            taylor_answers = EXCLUDED.taylor_answers,
            lyrics_answers = EXCLUDED.lyrics_answers,
            incorrect_answers = EXCLUDED.incorrect_answers,
            groups_participated = EXCLUDED.groups_participated,
            total_points = EXCLUDED.total_points
        """,
        (
            str(user_id),
            achievements_data[user_id]["correct_answers"],
            achievements_data[user_id]["current_streak"],
            achievements_data[user_id]["highest_streak"],
            achievements_data[user_id]["quick_answers"],
            achievements_data[user_id]["taylor_answers"],
            achievements_data[user_id]["lyrics_answers"],
            achievements_data[user_id]["incorrect_answers"],
            achievements_data[user_id]["groups_participated"],
            achievements_data[user_id]["total_points"]
        )
    ))

    # Clean up
    if question_key in active_questions:
        active_questions[question_key]["answered"] = True
        # Remove alarm job
        if context.job_queue:
            for job in context.job_queue.get_jobs_by_name(f"alarm_{question_key}"):
                job.schedule_removal()
                logger.info(f"Removed alarm job for question {question_key}")

        # Delete alarm message if exists
        if "alarm_message_id" in active_questions[question_key]:
            try:
                await context.bot.delete_message(chat_id=chat_id, message_id=active_questions[question_key]["alarm_message_id"])
                logger.info(f"Deleted alarm message for question {question_key}")
            except Exception as e:
                logger.error(f"Failed to delete alarm message for question {question_key}: {e}")

            if active_questions.get(question_key) and "alarm_message_id" in active_questions[question_key]:
                del active_questions[question_key]["alarm_message_id"]

        # Remove question from active_questions
        del active_questions[question_key]
        logger.info(f"Question {question_key} removed from active_questions")

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
async def save_leaderboard(data, pool):
    async with pool.acquire() as conn:
        async with conn.transaction():
            await conn.execute("DELETE FROM leaderboard WHERE chat_id = ANY($1)", list(data.keys()))
            for chat_id, chat_data in data.items():
                for user_id, user_data in chat_data["players"].items():
                    await conn.execute("""
                        INSERT INTO leaderboard (chat_id, user_id, name, score)
                        VALUES ($1, $2, $3, $4)
                        ON CONFLICT (chat_id, user_id) DO UPDATE SET
                            name = EXCLUDED.name,
                            score = EXCLUDED.score
                    """, chat_id, user_id, user_data["name"], user_data["score"])
        logger.info("Leaderboard data saved to PostgreSQL.")
        return True

# Save global leaderboard data
async def save_global_leaderboard(data, pool):
    try:
        async with pool.acquire() as conn:
            async with conn.transaction():
                for user_id, user_data in data.items():
                    user_id = str(user_id)  # Ensure user_id is a string
                    # Insert or update user in global_leaderboard
                    await conn.execute("""
                        INSERT INTO global_leaderboard (user_id, name, score)
                        VALUES ($1, $2, $3)
                        ON CONFLICT (user_id) DO UPDATE SET
                            name = EXCLUDED.name,
                            score = EXCLUDED.score
                    """, user_id, user_data["name"], user_data["score"])

                    # Get existing groups for the user from the database
                    existing_groups = await conn.fetch("""
                        SELECT group_id FROM global_leaderboard_groups WHERE user_id = $1
                    """, user_id)
                    existing_group_ids = {row["group_id"] for row in existing_groups}

                    # Update or insert groups in global_leaderboard_groups
                    for group_id, group_data in user_data["groups"].items():
                        group_id = str(group_id)  # Ensure group_id is a string
                        await conn.execute("""
                            INSERT INTO global_leaderboard_groups (user_id, group_id, group_name, score)
                            VALUES ($1, $2, $3, $4)
                            ON CONFLICT (user_id, group_id) DO UPDATE SET
                                group_name = EXCLUDED.group_name,
                                score = EXCLUDED.score
                        """, user_id, group_id, group_data["group_name"], group_data["score"])

                        # Remove this group from the set of existing groups (since it's been updated)
                        existing_group_ids.discard(group_id)

                    # Remove any groups the user is no longer part of
                    for group_id in existing_group_ids:
                        await conn.execute("""
                            DELETE FROM global_leaderboard_groups
                            WHERE user_id = $1 AND group_id = $2
                        """, user_id, group_id)

        logger.info("Global leaderboard updated selectively in PostgreSQL.")
        return True
    except Exception as e:
        logger.error(f"Error saving global leaderboard: {e}", exc_info=True)
        return False

# Update global leaderboard when a player scores points
async def update_global_leaderboard(user_id, user_name, chat_id, group_name, points, pool):
    user_id = str(user_id)  # Ensure user_id is a string
    chat_id = str(chat_id)  # Ensure chat_id is a string
    global global_leaderboard

    try:
        # Initialize user data if not exists
        if user_id not in global_leaderboard:
            global_leaderboard[user_id] = {"name": user_name, "score": 0, "groups": {}}

        # Update user name and total score
        global_leaderboard[user_id]["name"] = user_name
        global_leaderboard[user_id]["score"] = global_leaderboard[user_id]["score"] + points

        # Update group-specific data
        if chat_id not in global_leaderboard[user_id]["groups"]:
            global_leaderboard[user_id]["groups"][chat_id] = {"group_name": group_name, "score": 0}
        global_leaderboard[user_id]["groups"][chat_id]["group_name"] = group_name
        global_leaderboard[user_id]["groups"][chat_id]["score"] += points

        # Save only the updated user’s data
        user_data = {user_id: global_leaderboard[user_id]}
        await save_global_leaderboard(user_data, pool)
        logger.info(f"Updated global leaderboard for user {user_id} in chat {chat_id}: +{points} points")
    except Exception as e:
        logger.error(f"Error updating global leaderboard for user {user_id}: {e}", exc_info=True)

# Get top 50 players from the global leaderboard
async def get_top_players(limit=50, pool=None):
    global_leaderboard = await load_global_leaderboard(pool)
    sorted_players = sorted(
        global_leaderboard.items(),
        key=lambda x: x[1]["score"],
        reverse=True
    )[:limit]  # Use limit instead of hardcoded 50
    return sorted_players

# FUNCTION TO GET THE TOP 10 PLAYERS BY LANGUAGE
async def get_top_players_by_language(language, pool=None):
    global_leaderboard = await load_global_leaderboard(pool)
    user_languages = await load_user_languages(pool)
    
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
async def get_top_groups(pool=None):
    global_leaderboard = await load_global_leaderboard(pool)
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

# Implementation of get_user_profile_photo
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
    if re.search(r'[\u3040-\u309F\u30A0-\u30FF\u4E00-\U0001FA6F]', text):
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
    
# Achievements
def update_achievements(user_id, correct_answers=0, current_streak=0, highest_streak=0, quick_answer=False, question_type=None, points=0, chat_id=None):
    global achievements_data
    user_id = str(user_id)
    earned_achievements = []

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
            "achievements": [],
            "_achievement_tracked_groups": set()
        }
    elif "_achievement_tracked_groups" not in achievements_data[user_id]:
        achievements_data[user_id]["_achievement_tracked_groups"] = set()

    user_data = achievements_data[user_id]

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

    if chat_id:
        current_chat_id_str = str(chat_id)
        if "_achievement_tracked_groups" not in user_data:
            user_data["_achievement_tracked_groups"] = set()
        if current_chat_id_str not in user_data["_achievement_tracked_groups"]:
            user_data["_achievement_tracked_groups"].add(current_chat_id_str)
            user_data["groups_participated"] += 1
            logger.info(f"User {user_id} (via update_achievements): new group {current_chat_id_str} recorded for participation. Total groups_participated: {user_data['groups_participated']}")

    for ach_id, ach_data in ACHIEVEMENTS.items():
        if ach_id in user_data["achievements"]:
            continue
        
        threshold = ach_data.get("threshold")
        if threshold is None:
            logger.warning(f"Achievement {ach_id} is missing a 'threshold'. Skipping.")
            continue

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
            if isinstance(threshold, dict):
                 achieved = (user_data["correct_answers"] >= threshold.get("correct", float('inf')) and
                             user_data["quick_answers"] >= threshold.get("quick", float('inf')))
            else: 
                 achieved = (user_data["correct_answers"] >= threshold and user_data["quick_answers"] >= 1)
        elif ach_id == "bad_blood_buster":
            achieved = user_data["incorrect_answers"] >= threshold
        elif ach_id == "swiftie_supreme":
            other_achievements = set(ACHIEVEMENTS.keys()) - {"swiftie_supreme"}
            achieved = all(other_ach_id in user_data["achievements"] for other_ach_id in other_achievements)

        if achieved:
            user_data["achievements"].append(ach_id)
            earned_achievements.append(ach_id)
            logger.info(f"User {user_id} earned achievement: {ach_id}")

    return earned_achievements, user_data

# Profile picture
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
        logo = logo.resize((120, 120))  # Resize the logo to fit

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
    
# Profile Command  
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
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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

    # Fetch user's profile photo
    profile_photo_path = await get_user_profile_photo(user_id)

    # Load data
    leaderboard_data = await load_leaderboard(context.bot_data["db_pool"])
    streak_data = await load_streak_data(context.bot_data["db_pool"])
    achievements_data = await load_achievements_data(context.bot_data["db_pool"])
    global_leaderboard = await load_global_leaderboard(context.bot_data["db_pool"])

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
    global_rank = await get_global_rank(user_id, context.bot_data["db_pool"])

    # Get user's achievements (include both unnotified and notified)
    user_achievements_data = achievements_data.get(user_id, {})
    user_achievements = user_achievements_data.get("achievements", []) + user_achievements_data.get("notified_achievements", [])

    # Get user's emoji from USER_EMOJIS (backed by user_emojis table)
    user_emoji = get_emoji_for_user(user_id)

    # Generate profile image
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

    # Create the "Close" button
    keyboard = [
        [InlineKeyboardButton(localized["close_button"], callback_data="profile_close")]
    ]
    reply_markup = InlineKeyboardMarkup(keyboard)

    # Send the profile image and message with the close button
    await context.bot.send_photo(
        chat_id=chat_id,
        photo=profile_image,
        caption=profile_message,
        parse_mode=ParseMode.HTML,
        reply_markup=reply_markup
    )

    # Clean up the temporary profile photo file
    if profile_photo_path and os.path.exists(profile_photo_path):
        os.remove(profile_photo_path)

# Profile Callback
async def profile_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data

    if data == "profile_close":
        try:
            await query.message.delete()
            logger.info(f"Profile message deleted for user {query.from_user.id} in chat {query.message.chat_id}")
        except Exception as e:
            logger.error(f"Failed to delete profile message: {e}")
            await query.answer("❌ Failed to close profile.", show_alert=True)
        await query.answer()

# Generate leaderboard image dynamically
async def generate_leaderboard_image(chat_id, pool):
    async with IMAGE_GEN_SEMAPHORE:  # Limit concurrent generations
        group_settings = await load_group_settings(pool)
        group_language = group_settings.get(str(chat_id), {}).get("language", "en")
        logger.info(f"Generating leaderboard for chat {chat_id} with language {group_language}")

        leaderboard_data = await load_leaderboard(pool)
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
        name_start_y = 760
        rounded_rect_start_x = 1400
        rounded_rect_start_y = 760
        rounded_rect_width_max = 4000
        rounded_rect_height = 185
        rounded_rect_fill = "white"
        rounded_rect_outline = "white"
        rounded_rect_radius = 120
        normal_rect_start_x = 1400
        normal_rect_start_y = 760
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
async def generate_streak_leaderboard_image(chat_id, pool):
    async with IMAGE_GEN_SEMAPHORE:
        group_settings = await load_group_settings(pool)
        group_language = group_settings.get(str(chat_id), {}).get("language", "en")
        logger.info(f"Generating streak leaderboard for chat {chat_id} with language {group_language}")

        streak_data = await load_streak_data(pool)
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
        name_start_y = 760
        rounded_rect_start_x = 1400
        rounded_rect_start_y = 760
        rounded_rect_width_max = 4000
        rounded_rect_height = 185
        rounded_rect_fill = "white"
        rounded_rect_outline = "white"
        rounded_rect_radius = 120
        normal_rect_start_x = 1400
        normal_rect_start_y = 760
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
async def get_top_global_streaks(language=None, limit=10, pool=None):
    """Get top global streaks, optionally filtered by language."""
    global streak_data, user_languages
    streak_data = await load_streak_data(pool)
    user_languages = await load_user_languages(pool)
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    data = query.data
    chat_id = query.message.chat_id
    user_id = query.from_user.id
    group_settings = await load_group_settings(context.bot_data["db_pool"])
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    if data == "streak_local":
        if is_rate_limited(user_id, "streak_local"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        streak_image = await generate_streak_leaderboard_image(chat_id, context.bot_data["db_pool"])
        if streak_image:
            sorted_streaks = (await load_streak_data(context.bot_data["db_pool"])).get(str(chat_id), {})
            sorted_streaks = sorted(sorted_streaks.items(), key=lambda x: x[1]["streak"], reverse=True)[:10]
            caption = localized["local_title"]
            for index, (player_id, data) in enumerate(sorted_streaks, start=1):
                emoji = get_emoji_for_user(player_id)
                # Construct plain text entry to avoid HTML parsing issues
                caption += f"<b>{index}.</b> {emoji} {data['name']} — <b>{data['streak']}</b>\n"
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            # Add Close button
            keyboard = [[InlineKeyboardButton(localized["close_button"], callback_data="streak_local_close")]]
            reply_markup = InlineKeyboardMarkup(keyboard)
            try:
                await context.bot.send_photo(
                    chat_id=chat_id, photo=streak_image, caption=caption, parse_mode=ParseMode.HTML,
                    protect_content=True, has_spoiler=True, read_timeout=30, write_timeout=30, connect_timeout=30,
                    reply_markup=reply_markup
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
        if is_rate_limited(user_id, "streak_global"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        global_streaks = await get_top_global_streaks(pool=context.bot_data["db_pool"])
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

    elif data == "streak_show_languages":
        if is_rate_limited(user_id, "streak_show_languages"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        global_streaks = await get_top_global_streaks(pool=context.bot_data["db_pool"])
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

    elif data.startswith("lang_streak_"):
        if is_rate_limited(user_id, data):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        selected_lang = data.split("_")[2]
        if selected_lang == "overall":
            global_streaks = await get_top_global_streaks(pool=context.bot_data["db_pool"])
            caption = localized["global_title"]
        else:
            global_streaks = await get_top_global_streaks(language=selected_lang, pool=context.bot_data["db_pool"])
            flag = LANGUAGE_FLAGS.get(selected_lang, "🏳️")
            caption = localized["top_players_lang_title"].format(flag=flag)
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
             InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]
        ]
        await query.message.edit_text(
            caption, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
        )

    elif data == "streak_back":
        keyboard = [
            [InlineKeyboardButton(localized["group_button"], callback_data="streak_local"),
             InlineKeyboardButton(localized["global_button"], callback_data="streak_global")],
            [InlineKeyboardButton(localized["close_button"], callback_data="streak_cancel")]
        ]
        await query.message.edit_text(
            localized["options"], parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(keyboard)
        )

    elif data == "streak_cancel":
        await query.message.delete()

    elif data == "streak_local_close":
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    group_settings = await load_group_settings(context.bot_data["db_pool"])
    group_language = group_settings.get(str(chat_id), {}).get("language", "en")
    localized = localization.get(group_language, localization["en"])

    if data == "leaderboard_local":
        if is_rate_limited(user_id, "leaderboard_local"):
            await query.answer(localized["button_rate_limit"], show_alert=True)
            return
        leaderboard_image = await generate_leaderboard_image(chat_id, context.bot_data["db_pool"])
        if leaderboard_image:
            sorted_players = (await load_leaderboard(context.bot_data["db_pool"])).get(str(chat_id), {}).get("players", {})
            sorted_players = sorted(sorted_players.items(), key=lambda x: x[1]["score"], reverse=True)[:MAX_PLAYERS]
            caption = localized["local_rankings_title"]
            for index, (player_id, data) in enumerate(sorted_players, start=1):
                emoji = get_emoji_for_user(player_id)
                # Construct plain text entry to avoid HTML parsing issues
                caption += f"<b>{index}.</b> {emoji} {data['name']} — <b>{data['score']}</b>\n"
            # Add Close button
            keyboard = [[InlineKeyboardButton(localized["close_button"], callback_data="leaderboard_local_close")]]
            reply_markup = InlineKeyboardMarkup(keyboard)
            try:
                await context.bot.send_photo(
                    chat_id=chat_id, photo=leaderboard_image, caption=caption, parse_mode=ParseMode.HTML,
                    protect_content=True, has_spoiler=True, read_timeout=30, write_timeout=30, connect_timeout=30,
                    reply_markup=reply_markup
                )
                await query.message.delete()
            except telegram.error.TimedOut:
                await query.message.edit_text(localized["timeout_error"])
            except Exception as e:
                logger.error(f"Unexpected error: {e}")
                await query.message.edit_text(localized["generic_error"])
        else:
            await query.message.edit_text(localized["no_local_rankings"], parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]]))

    elif data == "leaderboard_top_players":
        top_players = await get_top_players(limit=10, pool=context.bot_data["db_pool"])
        if top_players:
            caption = localized["top_players_title"]
            for index, (player_id, data) in enumerate(top_players, start=1):
                emoji = get_emoji_for_user(player_id)
                caption += localized["top_player_entry"].format(
                    index=index, emoji=emoji, user_id=player_id, name=data["name"], score=data["score"]
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
        top_players = await get_top_players(limit=10, pool=context.bot_data["db_pool"])
        caption = localized["top_players_title"]
        for index, (player_id, data) in enumerate(top_players, start=1):
            emoji = get_emoji_for_user(player_id)
            caption += localized["top_player_entry"].format(
                index=index, emoji=emoji, user_id=player_id, name=data["name"], score=data["score"]
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
            [flag_buttons[0]],
            flag_buttons[1:4],
            flag_buttons[4:7],
            flag_buttons[7:10],
            flag_buttons[10:13],
            [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]
        ]
        reply_markup = InlineKeyboardMarkup(keyboard)
        if len(caption) > 4096:
            caption = caption[:4090] + "..."
        await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)

    elif data == "leaderboard_top_groups":
        top_groups = await get_top_groups(pool=context.bot_data["db_pool"])
        if top_groups:
            caption = localized["top_groups_title"]
            for index, (group_id, data) in enumerate(top_groups, start=1):
                caption += localized["top_group_entry"].format(
                    index=index, name=data["name"], score=data["score"]
                )
            keyboard = [
                [InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back"),
                 InlineKeyboardButton(localized["close_button"], callback_data="leaderboard_cancel")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            if len(caption) > 4096:
                caption = caption[:4090] + "..."
            await query.message.edit_text(caption, parse_mode=ParseMode.HTML, reply_markup=reply_markup)
        else:
            await query.message.edit_text(
                localized["no_top_groups"],
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton(localized["back_button"], callback_data="leaderboard_back")]])
            )

    elif data.startswith("lang_top_"):
        selected_option = data.split("_")[2]
        if selected_option == "overall":
            top_players = await get_top_players(limit=10, pool=context.bot_data["db_pool"])
            caption = localized["top_players_title"]
            if top_players:
                for index, (player_id, data) in enumerate(top_players, start=1):
                    emoji = get_emoji_for_user(player_id)
                    caption += localized["top_player_entry"].format(
                        index=index, emoji=emoji, user_id=player_id, name=data["name"], score=data["score"]
                    )
            else:
                caption = localized["no_top_players"]
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
            top_players = await get_top_players_by_language(selected_option, pool=context.bot_data["db_pool"])
            flag = LANGUAGE_FLAGS.get(selected_option, "🏳️")
            caption = localized["top_players_lang_title"].format(flag=flag)
            if top_players:
                for index, (player_id, data) in enumerate(top_players, start=1):
                    emoji = get_emoji_for_user(player_id)
                    caption += localized["top_player_entry"].format(
                        index=index, emoji=emoji, user_id=player_id, name=data["name"], score=data["score"]
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
                [flag_buttons[0]],
                flag_buttons[1:4],
                flag_buttons[4:7],
                flag_buttons[7:10],
                flag_buttons[10:13],
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

    elif data == "leaderboard_local_close":
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
        group_language = group_settings.get(str(chat.id), {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await update.message.reply_text(localized["admin_only"], parse_mode=ParseMode.HTML)
        return

    # Load group settings
    group_settings = await load_group_settings(context.bot_data["db_pool"])
    chat_id = str(chat.id)  # Ensure chat_id is a string

    # Initialize settings for this group if not present, including group name
    if chat_id not in group_settings:
        group_settings[chat_id] = {
            "group_name": chat.title,  # Add group name from chat object
            "answer_mode": "buttons",
            "quiz_interval": None,
            "language": "en"
        }
    # Update group name if it's missing or has changed
    elif "group_name" not in group_settings[chat_id] or group_settings[chat_id]["group_name"] != chat.title:
        group_settings[chat_id]["group_name"] = chat.title

    # Save the updated settings
    await save_group_settings(group_settings, context.bot_data["db_pool"])

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

# Updated settings_callback function
async def settings_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data
    chat_id = str(query.message.chat_id)  # Ensure chat_id is a string
    user_id = query.from_user.id

    # Check if the user is an admin or owner
    chat_member = await context.bot.get_chat_member(chat_id, user_id)
    if chat_member.status not in [ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER]:
        group_settings = await load_group_settings(context.bot_data["db_pool"])
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await query.answer(localized["admin_only"], show_alert=True)
        return

    # Load group settings
    group_settings = await load_group_settings(context.bot_data["db_pool"])
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

    group_language_current = group_settings[chat_id].get("language", "en")
    localized = localization.get(group_language_current, localization["en"])

    try:
        if data == "settings_menu":
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
            await query.answer()

        elif data == "settings_set_interval":
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
            await query.answer()

        elif data.startswith("interval_"):
            interval = int(data.split("_")[1])
            group_settings[chat_id]["quiz_interval"] = interval
            await save_group_settings(group_settings, context.bot_data["db_pool"])
            await schedule_quiz_jobs(context.job_queue, chat_id, interval, context.bot_data["db_pool"])

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
            await query.answer()


        elif data == "settings_stop_quiz":
            group_settings[chat_id]["quiz_interval"] = None
            await save_group_settings(group_settings, context.bot_data["db_pool"])
            # Remove jobs for this chat if they exist
            # (This logic would need to be more specific if jobs are uniquely named per chat)
            # For now, we rely on schedule_quiz_jobs to handle clearing/recreating general interval jobs
            # or perhaps a function like clear_quiz_jobs_for_chat(job_queue, chat_id)
            logger.info(f"Quiz stopped for chat {chat_id}. Associated jobs might need manual review or a specific clearing mechanism.")

            keyboard = [
                [InlineKeyboardButton(localized["stop_quiz_button"], callback_data="settings_stop_quiz")], # Might need to indicate it's stopped
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
                localized["interval_prompt"], # Or a message indicating quiz is stopped
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.HTML
            )
            await query.answer(localized["quiz_stopped"], show_alert=True)


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
            await query.answer()

        elif data == "confirm_reset_yes":
            if await reset_leaderboard(chat_id, context.bot_data["db_pool"]):
                await query.answer(localized["reset_success"], show_alert=True)
            else:
                await query.answer(localized["reset_fail"], show_alert=True)
            
            # Go back to main settings menu
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
            # query.answer already called with alert

        elif data == "confirm_reset_no":
            # Go back to main settings menu
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
            await query.answer()


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
            await query.answer()

        elif data.startswith("answer_mode_"):
            mode = data.split("_")[2] # "buttons" or "write"
            group_settings[chat_id]["answer_mode"] = mode
            await save_group_settings(group_settings, context.bot_data["db_pool"])

            keyboard = [
                [InlineKeyboardButton(f"{'✅ ' if mode == 'buttons' else '›› '}{localized['mode_buttons']}", callback_data="answer_mode_buttons"),
                 InlineKeyboardButton(f"{'✅ ' if mode == 'write' else '›› '}{localized['mode_write']}", callback_data="answer_mode_write")],
                [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
            ]
            await query.message.edit_text(
                localized["mode_prompt"], # Or a confirmation message like "Answer mode set to {mode}"
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.HTML
            )
            await query.answer()


        elif data == "settings_language":
            current_language_for_display = group_settings[chat_id].get("language", "en")
            # Localized is already set based on current_group_lang at the start of the function.
            # The message text "language_message" should use that existing localization.
            # The keyboard checkmarks should reflect current_language_for_display.
            keyboard = [
                [InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'en' else '›› '}🇺🇸EN", callback_data="language_en"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'es' else '›› '}🇪🇸ES", callback_data="language_es"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'ar' else '›› '}🇸🇦AR", callback_data="language_ar")],
                [InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'fa' else '›› '}🇮🇷FA", callback_data="language_fa"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'de' else '›› '}🇩🇪DE", callback_data="language_de"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'fr' else '›› '}🇫🇷FR", callback_data="language_fr")],
                [InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'it' else '›› '}🇮🇹IT", callback_data="language_it"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'pt' else '›› '}🇵🇹PT", callback_data="language_pt"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'id' else '›› '}🇮🇩ID", callback_data="language_id")],
                [InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'ko' else '›› '}🇰🇷KR", callback_data="language_ko"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'ru' else '›› '}🇷🇺RU", callback_data="language_ru"),
                 InlineKeyboardButton(f"{'✅ ' if current_language_for_display == 'tr' else '›› '}🇹🇷TR", callback_data="language_tr")],
                [InlineKeyboardButton(localized["back_button"], callback_data="settings_back")]
            ]
            await query.message.edit_text(
                localized["language_message"], # Text is in the group's current language (group_language_current)
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.HTML
            )
            await query.answer()

        elif data.startswith("language_"): # This is for setting a new language
            new_language_code = data.split("_")[1]
            logger.info(f"Attempting to set language to {new_language_code} for chat_id {chat_id}")

            current_group_lang = group_settings[chat_id].get("language", "en")

            if current_group_lang == new_language_code:
                logger.info(f"Language for chat {chat_id} is already {new_language_code}. No change needed.")
                # Even if no change, ensure keyboard reflects the current state and message is in this language.
                localized_current = localization.get(current_group_lang, localization["en"])
                keyboard = [
                    [InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'en' else '›› '}🇺🇸EN", callback_data="language_en"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'es' else '›› '}🇪🇸ES", callback_data="language_es"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'ar' else '›› '}🇸🇦AR", callback_data="language_ar")],
                    [InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'fa' else '›› '}🇮🇷FA", callback_data="language_fa"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'de' else '›› '}🇩🇪DE", callback_data="language_de"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'fr' else '›› '}🇫🇷FR", callback_data="language_fr")],
                    [InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'it' else '›› '}🇮🇹IT", callback_data="language_it"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'pt' else '›› '}🇵🇹PT", callback_data="language_pt"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'id' else '›› '}🇮🇩ID", callback_data="language_id")],
                    [InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'ko' else '›› '}🇰🇷KR", callback_data="language_ko"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'ru' else '›› '}🇷🇺RU", callback_data="language_ru"),
                     InlineKeyboardButton(f"{'✅ ' if current_group_lang == 'tr' else '›› '}🇹🇷TR", callback_data="language_tr")],
                    [InlineKeyboardButton(localized_current["back_button"], callback_data="settings_back")]
                ]
                try:
                    await query.message.edit_text(
                        localized_current["language_message"],
                        reply_markup=InlineKeyboardMarkup(keyboard),
                        parse_mode=ParseMode.HTML
                    )
                except telegram.error.BadRequest as e:
                    if "Message is not modified" in str(e):
                        logger.info("Message was not modified (already correct state).")
                    else:
                        raise # Re-raise other BadRequest errors
                await query.answer() 
                return

            group_settings[chat_id]["language"] = new_language_code
            await save_group_settings(group_settings, context.bot_data["db_pool"])
            logger.info(f"Updated group_settings for chat {chat_id}: {group_settings[chat_id]}")

            localized_new = localization.get(new_language_code, localization["en"])
            
            keyboard = [
                [InlineKeyboardButton(f"{'✅ ' if new_language_code == 'en' else '›› '}🇺🇸EN", callback_data="language_en"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'es' else '›› '}🇪🇸ES", callback_data="language_es"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'ar' else '›› '}🇸🇦AR", callback_data="language_ar")],
                [InlineKeyboardButton(f"{'✅ ' if new_language_code == 'fa' else '›› '}🇮🇷FA", callback_data="language_fa"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'de' else '›› '}🇩🇪DE", callback_data="language_de"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'fr' else '›› '}🇫🇷FR", callback_data="language_fr")],
                [InlineKeyboardButton(f"{'✅ ' if new_language_code == 'it' else '›› '}🇮🇹IT", callback_data="language_it"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'pt' else '›› '}🇵🇹PT", callback_data="language_pt"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'id' else '›› '}🇮🇩ID", callback_data="language_id")],
                [InlineKeyboardButton(f"{'✅ ' if new_language_code == 'ko' else '›› '}🇰🇷KR", callback_data="language_ko"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'ru' else '›› '}🇷🇺RU", callback_data="language_ru"),
                 InlineKeyboardButton(f"{'✅ ' if new_language_code == 'tr' else '›› '}🇹🇷TR", callback_data="language_tr")],
                [InlineKeyboardButton(localized_new["back_button"], callback_data="settings_back")]
            ]
            await query.message.edit_text(
                localized_new["language_message"],
                reply_markup=InlineKeyboardMarkup(keyboard),
                parse_mode=ParseMode.HTML
            )
            await query.answer()


        elif data == "settings_back":
            current_group_lang_for_menu = group_settings[chat_id].get("language", "en")
            localized_for_menu = localization.get(current_group_lang_for_menu, localization["en"])

            keyboard = [
                [InlineKeyboardButton(localized_for_menu["interval_button"], callback_data="settings_set_interval"),
                 InlineKeyboardButton(localized_for_menu["reset_button"], callback_data="settings_reset_leaderboard")],
                [InlineKeyboardButton(localized_for_menu["mode_button"], callback_data="settings_set_mode"),
                 InlineKeyboardButton(localized_for_menu["language_button"], callback_data="settings_language")],
                [InlineKeyboardButton(localized_for_menu["close_button"], callback_data="settings_cancel")]
            ]
            reply_markup = InlineKeyboardMarkup(keyboard)
            await query.message.edit_text(
                localized_for_menu["menu"],
                reply_markup=reply_markup,
                parse_mode=ParseMode.HTML
            )
            await query.answer()

        elif data == "settings_cancel":
            await query.message.delete()
            await query.answer() # Acknowledge the deletion.

        else:
            # If no specific data matched, still answer the query to remove "loading" state
            await query.answer()

    except telegram.error.BadRequest as e:
        if "Message is not modified" in str(e):
            logger.info(f"Message not modified for chat {chat_id}, callback data: {data}. Telegram API did not allow edit.")
            await query.answer() # Acknowledge the button press
        else:
            logger.error(f"BadRequest in settings_callback for chat {chat_id}, data {data}: {e}", exc_info=True)
            try:
                await query.answer(localized.get("generic_error", "An error occurred."), show_alert=True)
            except Exception: # If query.answer also fails
                logger.error(f"Failed to even send error alert for chat {chat_id}, data {data}")
    except Exception as e:
        logger.error(f"Unexpected error in settings_callback for chat {chat_id}, data {data}: {e}", exc_info=True)
        try:
            # Try to use the initially loaded localized string if available
            error_message_key = "generic_error"
            alert_message = localized.get(error_message_key, localization.get("en", {}).get(error_message_key, "An error occurred."))
            await query.answer(alert_message, show_alert=True)
        except Exception: # If query.answer also fails
             logger.error(f"Failed to send generic error alert for chat {chat_id}, data {data}")

# Report question command       
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
        group_language = group_settings.get(chat_id, {}).get("language", "en")
        localized = localization.get(group_language, localization["en"])
        await update.message.reply_text(localized["report_no_reply"], parse_mode=ParseMode.HTML)
        return

    # Check if the replied-to message is a quiz question (photo + caption)
    if not (replied_to.photo and replied_to.caption):
        group_settings = await load_group_settings(context.bot_data["db_pool"])
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

    group_settings = await load_group_settings(context.bot_data["db_pool"])
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
    
# Error Handler
async def error_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    logger.error(f"Exception occurred: {context.error}", exc_info=True)

# GET BOT GROUPS
async def get_bot_groups(context: ContextTypes.DEFAULT_TYPE, pool) -> set:
    """Retrieve all group chat IDs where the bot is a member from the database."""
    bot_groups = set()
    try:
        async with pool.acquire() as conn:
            rows = await conn.fetch("SELECT chat_id FROM bot_groups")
            bot_groups = {row["chat_id"] for row in rows}
        logger.info(f"Retrieved {len(bot_groups)} groups the bot is a member of: {bot_groups}")
    except Exception as e:
        logger.error(f"Error retrieving bot groups from database: {e}")
    return bot_groups

# Handle bot when added to the group
async def handle_bot_added(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle the event when the bot is added to a group, using the adding user's language."""
    chat = update.message.chat
    if chat.type not in ["group", "supergroup"]:
        return  # Ignore if not a group or supergroup

    new_members = update.message.new_chat_members
    if not new_members:
        return  # No new members to process

    bot_id = context.bot.id

    # Check if the bot is among the new members
    if any(member.id == bot_id for member in new_members):
        # Get the user who added the bot
        adding_user = update.message.from_user
        if not adding_user:
            logger.warning("Could not determine the user who added the bot.")
            return

        user_id = str(adding_user.id)
        chat_id = str(chat.id)
        group_name = chat.title or "Unknown Group"

        # Save to bot_groups
        async with context.bot_data["db_pool"].acquire() as conn:
            await conn.execute(
                "INSERT INTO bot_groups (chat_id, group_name) VALUES ($1, $2) ON CONFLICT (chat_id) DO UPDATE SET group_name = $2",
                chat_id, group_name
            )
            logger.info(f"Added group {chat_id} ({group_name}) to bot_groups")

        # Load the user's language preference from private chat (default to "en")
        user_languages = await load_user_languages(context.bot_data["db_pool"])
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
        group_settings = await load_group_settings(context.bot_data["db_pool"])
        if chat_id not in group_settings:
            group_settings[chat_id] = {
                "group_name": chat.title,
                "answer_mode": "buttons",
                "quiz_interval": None,
                "language": "en"
            }
            await save_group_settings(group_settings, context.bot_data["db_pool"])
            logger.info(f"Initialized settings for new group {chat_id}: {group_settings[chat_id]}")

        # Message 1: Welcome + Taylor Swift channel button
        welcome_message = localized["group_welcome"]
        channel_keyboard = InlineKeyboardMarkup([ 
            [InlineKeyboardButton("𝑻𝒂𝒚𝒍𝒐𝒓 𝑺𝒘𝒊𝒇𝒕 𝑵𝒂𝒕𝒊𝒐𝒏 ✨", url="https://t.me/missamericanatsn")]
        ])

        # Message 2: Setup prompt + Settings/Language buttons
        setup_prompt = localized.get(
            "setup_prompt",
            "To get started and set up the quiz in this group, use <code>/settings</code> or tap the button below:"
        )
        settings_keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton(localized["settings_button"], callback_data="settings_menu"),
                InlineKeyboardButton(localized["language_button"], callback_data="settings_language")
            ]
        ])

        try:
            # Send welcome message
            await context.bot.send_message(
                chat_id=chat.id,
                text=welcome_message,
                parse_mode=ParseMode.HTML,
                reply_markup=channel_keyboard
            )
            logger.info(f"Sent welcome message to group {chat_id} in language {user_language}")

            # Send setup prompt with settings/language buttons
            await context.bot.send_message(
                chat_id=chat.id,
                text=setup_prompt,
                parse_mode=ParseMode.HTML,
                reply_markup=settings_keyboard
            )
            logger.info(f"Sent setup prompt to group {chat_id}")
        except Exception as e:
            logger.error(f"Failed to send welcome/setup messages to group {chat_id}: {e}")

# HANDLE BOT KICKED
async def handle_bot_kicked(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Handle the event when the bot is kicked from a group."""
    chat = update.message.chat
    if chat.type not in ["group", "supergroup"]:
        logger.debug(f"Ignoring left_chat_member update for non-group chat {chat.id}")
        return

    left_member = update.message.left_chat_member
    if not left_member:
        logger.debug(f"No left_chat_member data in update for chat {chat.id}")
        return

    bot_id = context.bot.id
    chat_id = str(chat.id)

    if left_member.id == bot_id:
        kicked_by = update.message.from_user.username or update.message.from_user.first_name
        logger.info(f"Bot was kicked from group {chat_id} ({chat.title}) by {kicked_by}")
        try:
            # Remove from bot_groups
            async with context.bot_data["db_pool"].acquire() as conn:
                await conn.execute("DELETE FROM bot_groups WHERE chat_id = $1", chat_id)
                logger.info(f"Removed group {chat_id} from bot_groups")

            # Clean up group settings only
            group_settings = await load_group_settings(context.bot_data["db_pool"])
            if chat_id in group_settings:
                del group_settings[chat_id]
                await save_group_settings(group_settings, context.bot_data["db_pool"])
                logger.info(f"Removed settings for group {chat_id}")
        except Exception as e:
            logger.error(f"Error during group cleanup for group {chat_id}: {e}")

# Language callback
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
            user_languages = await load_user_languages(context.bot_data["db_pool"])
            current_language = user_languages.get(user_id, "en")  # Load from PostgreSQL, default to "en"
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
                group_settings = await load_group_settings(context.bot_data["db_pool"])
                group_settings[chat_id]["language"] = language
                await save_group_settings(group_settings, context.bot_data["db_pool"])
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
                user_languages = await load_user_languages(context.bot_data["db_pool"])
                user_languages[user_id] = language
                await save_user_languages(user_languages, context.bot_data["db_pool"])
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
            user_languages = await load_user_languages(context.bot_data["db_pool"])
            current_language = user_languages.get(user_id, "en")  # Load from PostgreSQL
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

# Initialize scheduler with SEND QUESTION DELAYS FIX
scheduler = AsyncIOScheduler()
scheduler.configure({
    'misfire_grace_time': 600,
    'coalesce': True,
    'max_missed_ticks': 1,
    'jobstore_retry_interval': 0.1
})

# Initialize application
application = ApplicationBuilder().token(BOT_TOKEN).build()
application.job_queue.scheduler = scheduler

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
    application.add_handler(CallbackQueryHandler(profile_callback, pattern="^profile_close$"))  # New handler
    application.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, handle_bot_added))
    application.add_handler(MessageHandler(filters.StatusUpdate.LEFT_CHAT_MEMBER, handle_bot_kicked))
    application.add_error_handler(error_handler)
      
# Main
async def main():
    global leaderboard_data, global_leaderboard, streak_data, achievements_data, user_languages, USER_EMOJIS, application, client
    try:
        logger.info("Starting MastermindBot")
        logger.info(f"Using BOT_TOKEN: {BOT_TOKEN[:10]}...")
        logger.debug("Validating BOT_TOKEN format")
        if not BOT_TOKEN or not re.match(r'^\d+:[\w-]{35}$', BOT_TOKEN):
            logger.error(f"Invalid BOT_TOKEN format: {BOT_TOKEN[:10]}...")
            raise ValueError("Invalid BOT_TOKEN format")

        # Initialize database pool first
        logger.info("Initializing database pool")
        pool = await asyncpg.create_pool(dsn=POSTGRES_DSN, min_size=5, max_size=20)
        application.bot_data["db_pool"] = pool

        # Create database tables
        logger.info("Creating database tables")
        await init_database(pool)

        # Initialize user emojis
        logger.info("Loading user emojis")
        await initialize_user_emojis(pool)
        logger.info(f"Loaded {len(USER_EMOJIS)} user emojis from PostgreSQL")

        # Load other data
        logger.info("Loading leaderboard data")
        leaderboard_data = await load_leaderboard(pool)
        logger.info("Loading global leaderboard")
        global_leaderboard = await load_global_leaderboard(pool)
        logger.info("Loading streak data")
        streak_data = await load_streak_data(pool)
        logger.info("Loading achievements data")
        achievements_data = await load_achievements_data(pool)
        logger.info(f"Loaded achievements_data with {len(achievements_data)} users")
        logger.info("Loading user languages")
        user_languages = await load_user_languages(pool)
        logger.info("Loading group settings")
        group_settings = await load_group_settings(pool)
        logger.info(f"Loaded settings for {len(group_settings)} groups")

        # Configure bot
        logger.info("Setting bot commands")
        await set_bot_commands()
        logger.info("Loading templates")
        load_templates()

        # Configure scheduler
        logger.info("Configuring scheduler")
        scheduler = AsyncIOScheduler()
        scheduler.configure({'misfire_grace_time': 600})
        application.job_queue.scheduler = scheduler

        logger.info("Clearing existing jobs")
        for job in application.job_queue.jobs():
            job.schedule_removal()
            logger.info(f"Cleared job {job.name}")

        # Schedule batch jobs for all intervals
        logger.info("Scheduling batch jobs for all intervals")
        async with GLOBAL_SCHEDULING_LOCK:
            supported_intervals = {3600, 7200, 10800, 14400, 21600, 28800, 43200, 86400}
            active_intervals = {settings.get("quiz_interval") for settings in group_settings.values() if settings.get("quiz_interval")}
            for interval in active_intervals:
                if interval in supported_intervals:
                    prep_job_name = f"prepare_{interval}"
                    for job in application.job_queue.get_jobs_by_name(prep_job_name):
                        job.schedule_removal()
                        logger.info(f"Removed existing prep job {prep_job_name}")
                    send_job_name = f"batch_send_{interval}"
                    for job in application.job_queue.get_jobs_by_name(send_job_name):
                        job.schedule_removal()
                        logger.info(f"Removed existing send job {send_job_name}")
                    delay = get_next_interval_time(interval) - 60
                    application.job_queue.run_repeating(
                        prepare_questions_for_interval,
                        interval=interval,
                        first=delay,
                        name=prep_job_name,
                        data={"interval": interval}
                    )
                    logger.info(f"Scheduled prep job {prep_job_name} with first run in {delay}s")
                    application.job_queue.run_repeating(
                        send_questions_to_all_groups,
                        interval=interval,
                        first=delay + 60,
                        name=send_job_name,
                        data={"interval": interval}
                    )
                    logger.info(f"Scheduled send job {send_job_name} with first run in {delay + 60}s")

        logger.info("Starting job monitoring task")
        asyncio.create_task(log_active_jobs(application.job_queue))

        logger.info("Testing BOT_TOKEN with getWebhookInfo")
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(f"https://api.telegram.org/bot{BOT_TOKEN}/getWebhookInfo") as response:
                    response_text = await response.text()
                    if response.status != 200:
                        logger.error(f"BOT_TOKEN invalid: {response_text}")
                        raise ValueError(f"Invalid BOT_TOKEN: {response_text}")
                    logger.debug(f"getWebhookInfo response: {response_text}")
                    webhook_info = json.loads(response_text)
                    if webhook_info["result"]["pending_update_count"] > 0:
                        logger.warning(f"Pending updates detected: {webhook_info['result']['pending_update_count']}")
        except Exception as e:
            logger.error(f"Failed to validate BOT_TOKEN with getWebhookInfo: {e}")
            raise

        logger.info("Starting Telethon client")
        try:
            await client.start(bot_token=BOT_TOKEN)
            logger.info("Telethon client started successfully")
        except Exception as e:
            logger.error(f"Failed to start Telethon client: {e}")
            raise

        logger.info("Setting webhook")
        webhook_url = "https://amgmastermindbot.space/webhook"
        try:
            await application.bot.set_webhook(
                url=webhook_url,
                allowed_updates=["message", "callback_query", "chat_member"],
                drop_pending_updates=True
            )
            logger.info(f"Webhook set to {webhook_url}")
        except Exception as e:
            logger.error(f"Failed to set webhook: {e}")
            raise

        logger.info("Initializing application")
        await application.initialize()
        logger.info("Starting application")
        await application.start()

        logger.info("Setting up handlers")
        setup_handlers(application)

        logger.info("Starting webhook server")
        max_retries = 3
        for attempt in range(1, max_retries + 1):
            try:
                await application.updater.start_webhook(
                    listen="0.0.0.0",
                    port=8443,
                    url_path="/webhook",
                    webhook_url=webhook_url,
                    drop_pending_updates=True
                )
                logger.info("Bot running on 0.0.0.0:8443")
                break
            except Exception as e:
                logger.error(f"Attempt {attempt}/{max_retries} failed to start webhook server: {e}")
                if attempt == max_retries:
                    raise
                await asyncio.sleep(5)

        logger.info("Starting batch write task")
        asyncio.create_task(batch_write_to_db(pool))

        logger.info("Entering keep-alive loop")
        while True:
            await asyncio.sleep(3600)
    except asyncio.CancelledError:
        logger.info("Bot shutdown requested")
    except Exception as e:
        logger.error(f"Unexpected error in main(): {e}", exc_info=True)
        raise
    finally:
        logger.info("Shutting down")
        await shutdown(None, asyncio.get_running_loop())

async def shutdown(signum, loop):
    logger.info(f"Received signal {signum}. Shutting down...")
    try:
        # Save all critical data before closing the pool
        if "db_pool" in application.bot_data and not application.bot_data["db_pool"].is_closing():
            await save_leaderboard(leaderboard_data, application.bot_data["db_pool"])
            await save_global_leaderboard(global_leaderboard, application.bot_data["db_pool"])
            await save_streak_data(streak_data, application.bot_data["db_pool"])
            await save_achievements_data(achievements_data, application.bot_data["db_pool"])
            logger.info("All data saved to PostgreSQL.")

        # Stop and shutdown the application if running
        if application.running:
            await application.stop()
            await application.shutdown()
            logger.info("Telegram application shut down.")

        # Disconnect the Telethon client if connected
        if client.is_connected():
            await client.disconnect()
            logger.info("Telethon client disconnected.")

        # Close the database pool after all operations
        if "db_pool" in application.bot_data and not application.bot_data["db_pool"].is_closing():
            await application.bot_data["db_pool"].close()
            logger.info("Database pool closed.")

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
