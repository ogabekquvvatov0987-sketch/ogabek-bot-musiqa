import os
import asyncio
from datetime import datetime, timedelta, timezone
import aiosqlite
import logging

logger = logging.getLogger(__name__)


class _ConnectionContext:
    def __init__(self, database):
        self.database = database
        self.connection = None

    async def __aenter__(self):
        await self.database._connection_lock.acquire()
        try:
            if self.database._connection is None:
                self.database._connection = await aiosqlite.connect(
                    self.database.db_path,
                    timeout=30,
                )
                await self.database._connection.execute("PRAGMA busy_timeout = 30000")
                await self.database._connection.execute("PRAGMA foreign_keys = ON")
                await self.database._connection.execute("PRAGMA journal_mode = WAL")
                await self.database._connection.execute("PRAGMA synchronous = FULL")
            self.connection = self.database._connection
            return self.connection
        except Exception:
            self.database._connection_lock.release()
            raise

    async def __aexit__(self, exc_type, exc_value, traceback):
        if exc_type is not None and self.connection is not None:
            await self.connection.rollback()
        self.database._connection_lock.release()


class Database:
    def __init__(self, db_name='bot.db'):
        base_dir = os.path.dirname(os.path.abspath(__file__))
        self.db_path = os.path.join(base_dir, db_name)
        self._connection = None
        self._connection_lock = asyncio.Lock()

    def get_connection(self):
        """Boshqariladigan, qayta ishlatiladigan async SQLite ulanishini beradi."""
        return _ConnectionContext(self)

    async def close(self):
        """SQLite ulanishini to'g'ri yopadi."""
        async with self._connection_lock:
            if self._connection is not None:
                await self._connection.close()
                self._connection = None

    async def setup(self):
        """Bazani ishga tushirish: jadvallarni yaratish va migratsiyalarni bajarish"""
        async with self.get_connection() as conn:
            await self.create_tables(conn)
            await self._run_migrations(conn)
            # Migratsiyadan keyin ustunlar mavjud bo'ladi.
            await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_last_active ON users(last_active)")
            await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)")
            await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_banned ON users(is_banned)")
            await conn.commit()

    async def create_tables(self, conn):
        # 🚀 Optimallashtirish: WAL rejimi (tezlik va parallel yozish uchun)
        await conn.execute("PRAGMA journal_mode=WAL;")
        await conn.execute("PRAGMA synchronous=FULL;")
        # Asosiy jadvallar
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS users (
                     user_id INTEGER PRIMARY KEY,
                     username TEXT,
                     first_name TEXT,
                     last_name TEXT,
                     full_name TEXT,
                     region TEXT,
                     district TEXT,
                     neighborhood TEXT,
                     phone TEXT,
                     location TEXT,
                     is_banned INTEGER DEFAULT 0,
                     joined_at TEXT,
                     last_captcha_time TEXT,
                     captcha_failures INTEGER DEFAULT 0,
                     temp_block_until TEXT
            )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS captcha (
                     user_id INTEGER PRIMARY KEY,
                     challenge TEXT,
                     answer TEXT
            )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS active_chats (
                     user_id INTEGER PRIMARY KEY,
                     admin_id INTEGER
                 )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS feedback (
                    user_id INTEGER PRIMARY KEY,
                    liked INTEGER,
                    rating INTEGER,
                    comment TEXT
                )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS orders (
                    order_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    order_text TEXT,
                    status TEXT DEFAULT 'yangi',
                    created_at TEXT
                )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS user_backups (
                    backup_id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    full_name TEXT, 
                    region TEXT, 
                    district TEXT, 
                    neighborhood TEXT, 
                    phone TEXT, 
                    location TEXT, 
                    deleted_at TEXT, 
                    restored INTEGER DEFAULT 0 
                )""")

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS channels (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    link TEXT UNIQUE
                )
            """)
        # 🚀 Keshlashtirish jadvali (Linklar va File ID lar)
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS media_cache (
                    url_id TEXT PRIMARY KEY,
                    file_id TEXT,
                    media_type TEXT,
                    quality TEXT,
                    file_size INTEGER
                )
            """)

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS bot_logs (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    action TEXT,
                    user_id INTEGER,
                    details TEXT,
                    created_at TEXT
                )
            """)
        # 🚀 Sozlamalar jadvali
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS bot_settings (
                    key TEXT PRIMARY KEY,
                    value TEXT
                )
            """)

        await conn.execute("""
                CREATE TABLE IF NOT EXISTS download_stats (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    file_type TEXT,
                    created_at TEXT
                )
            """)

        # Saqlangan media uchun jadvallar
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS saved_videos (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    file_id TEXT NOT NULL,
                    caption TEXT,
                    saved_at TEXT,
                    is_deleted INTEGER DEFAULT 0,
                    UNIQUE(user_id, file_id)
                )
            """)
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS saved_music (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    file_id TEXT NOT NULL,
                    title TEXT,
                    duration INTEGER,
                    is_deleted INTEGER DEFAULT 0,
                    saved_at TEXT,
                    UNIQUE(user_id, file_id)
                )
            """)
        await conn.execute("""
                CREATE TABLE IF NOT EXISTS saved_images (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER,
                    file_id TEXT NOT NULL,
                    caption TEXT,
                    saved_at TEXT,
                    is_deleted INTEGER DEFAULT 0,
                    UNIQUE(user_id, file_id)
                )
            """)

        # 🚀 Indekslar (Tezlikni oshirish uchun)
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_is_banned ON users(is_banned)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_admin_special_active ON users(is_admin, is_special_user, last_active)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_captcha_user_id ON captcha(user_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_active_chats_admin_id ON active_chats(admin_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_feedback_user_id ON feedback(user_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_orders_user_id ON orders(user_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_media_cache_lookup ON media_cache(url_id, quality)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_user_backups_user_restored_deleted ON user_backups(user_id, restored, deleted_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_download_stats_user_id ON download_stats(user_id)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_download_stats_created_at ON download_stats(created_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_orders_status ON orders(status)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_orders_user_created_at ON orders(user_id, created_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_bot_logs_created_at ON bot_logs(created_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_saved_videos_user_deleted_saved ON saved_videos(user_id, is_deleted, saved_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_saved_music_user_deleted_saved ON saved_music(user_id, is_deleted, saved_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_saved_images_user_deleted_saved ON saved_images(user_id, is_deleted, saved_at)")
        await conn.execute("CREATE INDEX IF NOT EXISTS idx_users_last_active ON users(last_active)")
        await conn.commit()

    async def _run_migrations(self, conn):
        """Barcha schema o'zgarishlarini bir tranzaksiyada tekshiradi va qo'llaydi."""
        # --- `users` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('users')") as cursor:
            rows = await cursor.fetchall()
            user_columns = {col[1] for col in rows}
        
        user_migrations = {
            "pending_support": "ALTER TABLE users ADD COLUMN pending_support INTEGER DEFAULT 0",
            "last_active": "ALTER TABLE users ADD COLUMN last_active TEXT",
            "language": "ALTER TABLE users ADD COLUMN language TEXT DEFAULT 'uz'",
            "is_admin": "ALTER TABLE users ADD COLUMN is_admin INTEGER DEFAULT 0",
            "is_special_user": "ALTER TABLE users ADD COLUMN is_special_user INTEGER DEFAULT 0",
            "photo_id": "ALTER TABLE users ADD COLUMN photo_id TEXT",
            "complaint_sent": "ALTER TABLE users ADD COLUMN complaint_sent INTEGER DEFAULT 0",
            "captcha_failures": "ALTER TABLE users ADD COLUMN captcha_failures INTEGER DEFAULT 0",
            "temp_block_until": "ALTER TABLE users ADD COLUMN temp_block_until TEXT"
        }
        
        for col, query in user_migrations.items():
            if col not in user_columns:
                await conn.execute(query)
                logger.info(f"'{col}' ustuni 'users' jadvaliga muvaffaqiyatli qo'shildi ✅")

        # --- `feedback` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('feedback')") as cursor:
            rows = await cursor.fetchall()
            feedback_columns = {col[1] for col in rows}
        if "comment" not in feedback_columns: await conn.execute("ALTER TABLE feedback ADD COLUMN comment TEXT")
        if "liked" not in feedback_columns: await conn.execute("ALTER TABLE feedback ADD COLUMN liked INTEGER")
        if "rating" not in feedback_columns: await conn.execute("ALTER TABLE feedback ADD COLUMN rating INTEGER")

        # --- `orders` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('orders')") as cursor:
            rows = await cursor.fetchall()
            orders_columns = {col[1] for col in rows}
        if "order_type" not in orders_columns: await conn.execute("ALTER TABLE orders ADD COLUMN order_type TEXT")
        if "platform" not in orders_columns: await conn.execute("ALTER TABLE orders ADD COLUMN platform TEXT")
        if "media_file_id" not in orders_columns: await conn.execute("ALTER TABLE orders ADD COLUMN media_file_id TEXT")
        if "media_type" not in orders_columns: await conn.execute("ALTER TABLE orders ADD COLUMN media_type TEXT")

        # --- `media_cache` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('media_cache')") as cursor:
            rows = await cursor.fetchall()
            cache_columns = {col[1] for col in rows}
        if "title" not in cache_columns: await conn.execute("ALTER TABLE media_cache ADD COLUMN title TEXT")

        # --- `saved_music` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('saved_music')") as cursor:
            rows = await cursor.fetchall()
            music_columns = {col[1] for col in rows}
        if "duration" not in music_columns:
            await conn.execute("ALTER TABLE saved_music ADD COLUMN duration INTEGER")
            logger.info("'duration' ustuni 'saved_music' jadvaliga muvaffaqiyatli qo'shildi ✅")
        if "is_deleted" not in music_columns:
            await conn.execute("ALTER TABLE saved_music ADD COLUMN is_deleted INTEGER DEFAULT 0")
            logger.info("'is_deleted' ustuni 'saved_music' jadvaliga muvaffaqiyatli qo'shildi ✅")

        # --- `saved_images` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('saved_images')") as cursor:
            rows = await cursor.fetchall()
            images_columns = {col[1] for col in rows}
        if "is_deleted" not in images_columns:
            await conn.execute("ALTER TABLE saved_images ADD COLUMN is_deleted INTEGER DEFAULT 0")
            logger.info("'is_deleted' ustuni 'saved_images' jadvaliga muvaffaqiyatli qo'shildi ✅")

        # --- `saved_videos` jadvalini tekshirish ---
        async with conn.execute("PRAGMA table_info('saved_videos')") as cursor:
            rows = await cursor.fetchall()
            videos_columns = {col[1] for col in rows}
        if "is_deleted" not in videos_columns:
            await conn.execute("ALTER TABLE saved_videos ADD COLUMN is_deleted INTEGER DEFAULT 0")
            logger.info("'is_deleted' ustuni 'saved_videos' jadvaliga muvaffaqiyatli qo'shildi ✅")

        await conn.commit()

    async def add_download_stat(self, user_id, file_type):
        async with self.get_connection() as conn:
            await conn.execute("INSERT INTO download_stats (user_id, file_type, created_at) VALUES (?, ?, ?)",
                           (user_id, file_type, datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")))
            await conn.commit()

    async def save_video(self, user_id, file_id, caption):
        async with self.get_connection() as conn:
            cursor = await conn.execute("""
                INSERT INTO saved_videos (user_id, file_id, caption, saved_at)
                VALUES (?, ?, ?, ?)
                ON CONFLICT(user_id, file_id) DO UPDATE SET is_deleted = 0
            """, (user_id, file_id, caption, datetime.now().isoformat()))
            await conn.commit()
            return cursor.rowcount > 0

    async def get_saved_videos(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT id, file_id, caption FROM saved_videos WHERE user_id = ? AND is_deleted = 0 ORDER BY saved_at DESC", (user_id,)) as cursor:
                return await cursor.fetchall()

    async def delete_saved_video(self, video_db_id, user_id):
        async with self.get_connection() as conn:
            # Videoni butunlay o'chirmasdan, soft-delete qilish
            cursor = await conn.execute("UPDATE saved_videos SET is_deleted = 1 WHERE id = ? AND user_id = ?", (video_db_id, user_id))
            await conn.commit()
            return cursor.rowcount > 0
            
    async def update_video_caption(self, video_id, user_id, new_caption):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_videos SET caption = ? WHERE id = ? AND user_id = ?", (new_caption, video_id, user_id))
            await conn.commit()
            return cursor.rowcount > 0

    async def soft_delete_all_videos(self, user_id):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_videos SET is_deleted = 1 WHERE user_id = ?", (user_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def restore_all_videos(self, user_id):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_videos SET is_deleted = 0 WHERE user_id = ?", (user_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def has_deleted_videos(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT COUNT(*) FROM saved_videos WHERE user_id = ? AND is_deleted = 1", (user_id,)) as cursor:
                row = await cursor.fetchone()
                return row[0] > 0

    async def save_music(self, user_id, file_id, title, duration=None):
        async with self.get_connection() as conn:
            cursor = await conn.execute("""
                INSERT INTO saved_music (user_id, file_id, title, duration, saved_at)
                VALUES (?, ?, ?, ?, ?)
                ON CONFLICT(user_id, file_id) DO UPDATE SET is_deleted = 0
            """, (user_id, file_id, title, duration, datetime.now().isoformat()))
            await conn.commit()
            return cursor.rowcount > 0

    async def get_saved_music(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT id, file_id, title, duration FROM saved_music WHERE user_id = ? AND is_deleted = 0 ORDER BY saved_at DESC", (user_id,)) as cursor:
                return await cursor.fetchall()

    async def delete_saved_music(self, music_db_id, user_id):
        """Musiqani soft delete qilish"""
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_music SET is_deleted = 1 WHERE id = ? AND user_id = ?", (music_db_id, user_id))
            await conn.commit()
            return cursor.rowcount > 0

    async def soft_delete_all_music(self, user_id):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_music SET is_deleted = 1 WHERE user_id = ?", (user_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def restore_all_music(self, user_id):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_music SET is_deleted = 0 WHERE user_id = ?", (user_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def has_deleted_music(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT COUNT(*) FROM saved_music WHERE user_id = ? AND is_deleted = 1", (user_id,)) as cursor:
                row = await cursor.fetchone()
                return row[0] > 0

    async def update_music_title(self, music_db_id, user_id, new_title):
        """Musiqaning nomini yangilash"""
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_music SET title = ? WHERE id = ? AND user_id = ?", (new_title, music_db_id, user_id))
            await conn.commit()
            return cursor.rowcount > 0

    async def save_image(self, user_id, file_id, caption):
        async with self.get_connection() as conn:
            cursor = await conn.execute("""
                INSERT INTO saved_images (user_id, file_id, caption, saved_at)
                VALUES (?, ?, ?, ?)
                ON CONFLICT(user_id, file_id) DO UPDATE SET is_deleted = 0
            """, (user_id, file_id, caption, datetime.now().isoformat()))
            await conn.commit()
            return cursor.rowcount > 0

    async def get_saved_images(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT id, file_id, caption FROM saved_images WHERE user_id = ? AND is_deleted = 0 ORDER BY saved_at DESC", (user_id,)) as cursor:
                return await cursor.fetchall()

    async def delete_saved_image(self, image_db_id, user_id):
        """Rasmni soft delete qilish"""
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_images SET is_deleted = 1 WHERE id = ? AND user_id = ?", (image_db_id, user_id))
            await conn.commit()
            return cursor.rowcount > 0

    async def soft_delete_all_images(self, user_id):
        async with self.get_connection() as conn:
            cursor = await conn.execute("UPDATE saved_images SET is_deleted = 1 WHERE user_id = ?", (user_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def has_deleted_images(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT COUNT(*) FROM saved_images WHERE user_id = ? AND is_deleted = 1", (user_id,)) as cursor:
                row = await cursor.fetchone()
                return row[0] > 0

    async def delete_inactive_users(self, days: int = 7, batch_size: int = 500) -> int:
        """Bot bilan oxirgi aloqasi 7+ kun bo'lgan oddiy foydalanuvchilarni batch bilan o'chiradi."""
        days = max(1, int(days))
        batch_size = max(50, min(int(batch_size), 2000))
        cutoff = (datetime.now() - timedelta(days=days)).isoformat()
        total = 0
        async with self.get_connection() as conn:
            while True:
                async with conn.execute(
                    "SELECT user_id FROM users WHERE COALESCE(last_active, joined_at) < ? "
                    "AND COALESCE(is_admin, 0) = 0 AND COALESCE(is_special_user, 0) = 0 LIMIT ?",
                    (cutoff, batch_size),
                ) as cursor:
                    ids = [row[0] for row in await cursor.fetchall()]
                if not ids:
                    break

                placeholders = ",".join("?" for _ in ids)
                # Mavjud jadvallarning faqat borlarini tozalaymiz.
                for table in (
                    "captcha", "feedback", "active_chats", "saved_music", "saved_videos",
                    "saved_images", "download_stats", "orders", "bot_logs", "user_backups"
                ):
                    try:
                        await conn.execute(
                            f"DELETE FROM {table} WHERE user_id IN ({placeholders})", ids
                        )
                    except aiosqlite.OperationalError:
                        continue
                await conn.execute(
                    f"DELETE FROM users WHERE user_id IN ({placeholders})", ids
                )
                await conn.commit()
                total += len(ids)
                if len(ids) < batch_size:
                    break
        return total

    async def add_user(self, user_id, username, first_name, last_name):
        # Vaqtlar UTC bo'yicha timezone'siz ISO formatida saqlanadi; eski yozuvlar bilan mos.
        now = datetime.now(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")
        async with self.get_connection() as conn:
            await conn.execute("""
                INSERT INTO users (user_id, username, first_name, last_name, joined_at, last_active, captcha_failures, temp_block_until)
                VALUES (?, ?, ?, ?, ?, ?, 0, NULL)
                ON CONFLICT(user_id) DO UPDATE SET
                    username=excluded.username,
                    first_name=excluded.first_name,
                    last_name=excluded.last_name,
                    last_active=excluded.last_active
            """, (user_id, username, first_name, last_name, now, now))
            await conn.commit()

    async def get_user(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM users WHERE user_id = ?", (user_id,)) as cursor:
                return await cursor.fetchone()

    async def get_user_language(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT language FROM users WHERE user_id = ?", (user_id,)) as cursor:
                row = await cursor.fetchone()
                return row[0] if row and row[0] in {"uz", "ru", "en"} else "uz"

    async def set_user_language(self, user_id, language):
        if language not in {"uz", "ru", "en"}:
            raise ValueError("Noto'g'ri til kodi")
        await self.update_user_field(user_id, "language", language)

    async def update_user_field(self, user_id, field, value):
        allowed = {
            "full_name", "region", "district", "neighborhood", "photo_id", "complaint_sent",
            "phone", "location", "is_banned", "last_captcha_time", "pending_support", "last_active", "language",
            "is_admin", "is_special_user", "captcha_failures", "temp_block_until"
        }
        if field not in allowed:
            raise ValueError("Ruxsat etilmagan field")

        async with self.get_connection() as conn:
            # Ensure `last_active` is updated whenever any field is updated, unless we are only updating last_active
            if field != "last_active":
                await conn.execute(
                    f"UPDATE users SET {field} = ?, last_active = ? WHERE user_id = ?",
                    (value, datetime.now(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds"), user_id)
                )
            else:
                await conn.execute(
                    f"UPDATE users SET {field} = ? WHERE user_id = ?",
                    (value, user_id)
                )
            await conn.commit()

    async def update_last_captcha_time(self, user_id):
        await self.update_user_field(user_id, "last_captcha_time", datetime.now().isoformat())

    async def needs_captcha(self, user_id):
        user = await self.get_user(user_id)
        if not user or not user[12]: # last_captcha_time
            return True
        last_time = datetime.fromisoformat(user[12])
        return datetime.now() - last_time > timedelta(hours=24)

    async def set_captcha(self, user_id, challenge, answer):
        async with self.get_connection() as conn:
            await conn.execute("""
                INSERT OR REPLACE INTO captcha (user_id, challenge, answer)
                VALUES (?, ?, ?)
            """, (user_id, challenge, answer))
            await conn.commit()

    async def get_captcha(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT challenge, answer FROM captcha WHERE user_id = ?", (user_id,)) as cursor:
                res = await cursor.fetchone()
                return res or (None, None)

    async def remove_captcha(self, user_id):
        async with self.get_connection() as conn:
            await conn.execute("DELETE FROM captcha WHERE user_id = ?", (user_id,))
            await conn.commit()

    async def has_profile(self, user_id):
        user = await self.get_user(user_id)
        return user and user[4] is not None  # full_name bormi?

    async def delete_user_profile(self, user_id):
        user = await self.get_user(user_id)
        if not user:
            return
        async with self.get_connection() as conn:
            await conn.execute("""
                INSERT INTO user_backups (user_id, full_name, region, district, neighborhood, phone, location, deleted_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """, (user_id, user[4], user[5], user[6], user[7], user[8], user[9], datetime.now().isoformat()))

            await conn.execute("""
                UPDATE users SET full_name = NULL, region = NULL, district = NULL,
                neighborhood = NULL, phone = NULL, location = NULL WHERE user_id = ?
            """, (user_id,))
            await conn.commit()

    async def restore_user_profile(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("""
                SELECT backup_id, full_name, region, district, neighborhood, phone, location
                FROM user_backups WHERE user_id = ? AND restored = 0
                ORDER BY deleted_at DESC LIMIT 1
            """, (user_id,)) as cursor:
                backup_data = await cursor.fetchone()
            
            if backup_data:
                backup_id = backup_data[0]
                full_name, region, district, neighborhood, phone, location = backup_data[1:]
                
                await conn.execute("""
                    UPDATE users SET full_name = ?, region = ?, district = ?,
                    neighborhood = ?, phone = ?, location = ? WHERE user_id = ?
                """, (full_name, region, district, neighborhood, phone, location, user_id))
                
                await conn.execute("UPDATE user_backups SET restored = 1 WHERE backup_id = ?", (backup_id,))
                await conn.commit()
                return True
            return False

    async def has_deleted_profile(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT COUNT(*) FROM user_backups WHERE user_id = ? AND restored = 0", (user_id,)) as cursor:
                row = await cursor.fetchone()
                return row[0] > 0

    async def set_active_chat(self, user_id, admin_id):
        async with self.get_connection() as conn:
            await conn.execute("""
                INSERT OR REPLACE INTO active_chats (user_id, admin_id)
                VALUES (?, ?)
            """, (user_id, admin_id))
            await conn.commit()

    async def get_active_admin(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT admin_id FROM active_chats WHERE user_id = ?", (user_id,)) as cursor:
                result = await cursor.fetchone()
            return result[0] if result else None

    async def remove_active_chat(self, user_id):
        async with self.get_connection() as conn:
            await conn.execute("DELETE FROM active_chats WHERE user_id = ?", (user_id,))
            await conn.commit()

    async def save_feedback(self, user_id, liked=None, rating=None, comment=None):
        async with self.get_connection() as conn:
            # Avval borligini tekshiramiz
            async with conn.execute("SELECT * FROM feedback WHERE user_id = ?", (user_id,)) as cursor:
                exists = await cursor.fetchone()
            
            if not exists:
                await conn.execute("INSERT INTO feedback (user_id) VALUES (?)", (user_id,))
            
            if liked is not None:
                await conn.execute("UPDATE feedback SET liked = ? WHERE user_id = ?", (liked, user_id))
            if rating is not None:
                await conn.execute("UPDATE feedback SET rating = ? WHERE user_id = ?", (rating, user_id))
            if comment is not None:
                await conn.execute("UPDATE feedback SET comment = ? WHERE user_id = ?", (comment, user_id))
            await conn.commit()

    async def add_order(self, user_id, order_text, order_type=None, platform=None, media_file_id=None, media_type=None):
        now = datetime.now().isoformat()
        async with self.get_connection() as conn:
            cursor = await conn.execute("""
                INSERT INTO orders (user_id, order_text, created_at, order_type, platform, media_file_id, media_type)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            """, (user_id, order_text, now, order_type, platform, media_file_id, media_type))
            await conn.commit()
            return cursor.lastrowid

    async def get_order(self, order_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM orders WHERE order_id = ?", (order_id,)) as cursor:
                return await cursor.fetchone()

    async def get_orders(self):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM orders WHERE status = 'yangi' OR status = 'Keyinroq ⏳' ORDER BY created_at DESC") as cursor:
                return await cursor.fetchall()

    async def update_order_status(self, order_id, status):
        async with self.get_connection() as conn:
            await conn.execute("UPDATE orders SET status = ? WHERE order_id = ?", (status, order_id))
            await conn.commit()

    async def delete_order(self, order_id):
        """Buyurtmani ID bo'yicha o'chirish"""
        async with self.get_connection() as conn:
            cursor = await conn.execute("DELETE FROM orders WHERE order_id = ?", (order_id,))
            await conn.commit()
            return cursor.rowcount > 0

    async def cleanup_inactive_users(self, inactive_days=7, batch_size=500, preserve_admins=True):
        """
        Bot bilan oxirgi aloqasi inactive_days dan oshgan foydalanuvchilarni
        va ularga tegishli ma'lumotlarni bitta tranzaksiyada o'chiradi.

        Eslatma: Telegram Bot API foydalanuvchining haqiqiy online/last-seen
        vaqtini bermaydi. Shu sababli bu yerda `last_active` = bot bilan oxirgi
        qayd etilgan aloqa vaqti hisoblanadi. Admin va special userlar default
        bo'yicha saqlab qolinadi.
        """
        if not isinstance(inactive_days, int) or inactive_days < 1:
            raise ValueError("inactive_days 1 yoki undan katta butun son bo'lishi kerak")
        if not isinstance(batch_size, int) or batch_size < 1:
            raise ValueError("batch_size 1 yoki undan katta butun son bo'lishi kerak")

        cutoff = (datetime.now(timezone.utc) - timedelta(days=inactive_days)).isoformat(timespec="seconds")
        deleted_total = 0

        while True:
            async with self.get_connection() as conn:
                admin_clause = "" if preserve_admins else "AND 1=1"
                if preserve_admins:
                    admin_clause = "AND COALESCE(is_admin, 0) = 0 AND COALESCE(is_special_user, 0) = 0"

                async with conn.execute(
                    f"SELECT user_id FROM users WHERE (last_active IS NULL OR last_active < ?) {admin_clause} LIMIT ?",
                    (cutoff, batch_size),
                ) as cursor:
                    rows = await cursor.fetchall()

                if not rows:
                    await conn.execute("PRAGMA wal_checkpoint(PASSIVE)")
                    return deleted_total

                user_ids = [row[0] for row in rows]
                placeholders = ",".join("?" for _ in user_ids)

                # Bog'liq yozuvlarni avval o'chirish: schema'da FK CASCADE
                # yo'qligi sababli orphan ma'lumot qolib ketmasin.
                for table in (
                    "captcha", "feedback", "user_backups", "saved_music",
                    "saved_videos", "saved_images", "download_stats",
                    "orders", "active_chats", "bot_logs"
                ):
                    await conn.execute(
                        f"DELETE FROM {table} WHERE user_id IN ({placeholders})",
                        user_ids,
                    )

                cur = await conn.execute(
                    f"DELETE FROM users WHERE user_id IN ({placeholders})",
                    user_ids,
                )
                await conn.commit()
                deleted_total += cur.rowcount

                if cur.rowcount < len(user_ids):
                    # Biror parallel jarayon userni qayta yaratgan bo'lsa,
                    # keyingi batch qolganlarini xavfsiz davom ettiradi.
                    continue


    async def get_all_users(self):
        # Exclude Telegram's service accounts
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM users WHERE user_id NOT IN (777000, 1087968824) ORDER BY user_id DESC") as cursor:
                return await cursor.fetchall()

    async def get_users_paginated(self, limit, offset):
        """Foydalanuvchilarni sahifalab olish (Optimallashtirilgan)"""
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM users WHERE user_id NOT IN (777000, 1087968824) ORDER BY user_id DESC LIMIT ? OFFSET ?", (limit, offset)) as cursor:
                return await cursor.fetchall()

    async def get_users_count(self):
        """Jami foydalanuvchilar sonini olish"""
        async with self.get_connection() as conn:
            # Exclude Telegram's service accounts
            async with conn.execute("SELECT COUNT(*) FROM users WHERE user_id NOT IN (777000, 1087968824)") as cursor:
                row = await cursor.fetchone()
                return row[0]

    async def get_banned_users(self):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM users WHERE is_banned = 1") as cursor:
                return await cursor.fetchall()

    async def ban_user(self, user_id):
        await self.update_user_field(user_id, "is_banned", 1)

    async def delete_user(self, user_id):
        """Foydalanuvchini va unga bog'liq barcha ma'lumotlarni o'chirish"""
        async with self.get_connection() as conn:
            await conn.execute("DELETE FROM users WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM captcha WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM feedback WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM user_backups WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM saved_music WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM saved_videos WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM saved_images WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM download_stats WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM orders WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM active_chats WHERE user_id = ?", (user_id,))
            await conn.execute("DELETE FROM bot_logs WHERE user_id = ?", (user_id,))
            await conn.commit()

    async def is_pending_support(self, user_id):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT pending_support FROM users WHERE user_id = ?", (user_id,)) as cursor:
                result = await cursor.fetchone()
            return bool(result[0]) if result else False

    async def is_user_admin(self, user_id):
        """Foydalanuvchining admin ekanligini tekshiradi (DB bo'yicha)"""
        async with self.get_connection() as conn:
            async with conn.execute("SELECT is_admin FROM users WHERE user_id = ?", (user_id,)) as cursor:
                result = await cursor.fetchone()
            return bool(result[0]) if result else False

    async def is_special_user(self, user_id):
        """Foydalanuvchining maxsus ruxsatga ega ekanligini tekshiradi"""
        async with self.get_connection() as conn:
            async with conn.execute("SELECT is_special_user FROM users WHERE user_id = ?", (user_id,)) as cursor:
                result = await cursor.fetchone()
            return bool(result[0]) if result else False

    async def set_pending_support(self, user_id, value: bool):
        await self.update_user_field(user_id, "pending_support", 1 if value else 0)

    async def get_stats(self):
        uz_timezone = timezone(timedelta(hours=5))
        now_uz = datetime.now(uz_timezone)
        today_start_uz = now_uz.replace(hour=0, minute=0, second=0, microsecond=0)
        tomorrow_start_uz = today_start_uz + timedelta(days=1)
        week_start_uz = today_start_uz - timedelta(days=today_start_uz.weekday())
        month_start_uz = today_start_uz.replace(day=1)

        # DBdagi vaqtlar UTC; statistik chegaralarni UTC ga o'tkazamiz.
        today_start = today_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")
        tomorrow_start = tomorrow_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")
        week_start = week_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")
        month_start = month_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")

        async with self.get_connection() as conn:
            async with conn.execute("SELECT COUNT(*) FROM users") as cursor:
                total = (await cursor.fetchone())[0]
            async with conn.execute("SELECT COUNT(*) FROM users WHERE is_banned = 1") as cursor:
                banned = (await cursor.fetchone())[0]

            async with conn.execute(
                "SELECT COUNT(*) FROM users WHERE joined_at >= ? AND joined_at < ?",
                (today_start, tomorrow_start),
            ) as cursor:
                new_today = (await cursor.fetchone())[0]
            async with conn.execute(
                "SELECT COUNT(*) FROM users WHERE joined_at >= ?", (week_start,)
            ) as cursor:
                new_week = (await cursor.fetchone())[0]
            async with conn.execute(
                "SELECT COUNT(*) FROM users WHERE joined_at >= ?", (month_start,)
            ) as cursor:
                new_month = (await cursor.fetchone())[0]

            # download_stats eski yozuvlari timezone'siz bo'lishi mumkin;
            # yangi yozuvlar UTC bo'yicha yoziladi.
            async with conn.execute(
                "SELECT COUNT(*) FROM download_stats WHERE datetime(created_at) >= datetime(?) AND datetime(created_at) < datetime(?)",
                (today_start, tomorrow_start),
            ) as cursor:
                dl_today = (await cursor.fetchone())[0]
            async with conn.execute(
                "SELECT COUNT(*) FROM download_stats WHERE datetime(created_at) >= datetime(?)", (week_start,)
            ) as cursor:
                dl_week = (await cursor.fetchone())[0]
            async with conn.execute(
                "SELECT COUNT(*) FROM download_stats WHERE datetime(created_at) >= datetime(?)", (month_start,)
            ) as cursor:
                dl_month = (await cursor.fetchone())[0]

            return {
                "total": total, "banned": banned,
                "new_today": new_today, "new_week": new_week, "new_month": new_month,
                "dl_today": dl_today, "dl_week": dl_week, "dl_month": dl_month
            }

    async def get_user_daily_stats(self, user_id):
        """Foydalanuvchining O'zbekiston vaqti bo'yicha bugungi yuklashlar sonini oladi."""
        uz_timezone = timezone(timedelta(hours=5))
        today_start_uz = datetime.now(uz_timezone).replace(hour=0, minute=0, second=0, microsecond=0)
        tomorrow_start_uz = today_start_uz + timedelta(days=1)
        today_start = today_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")
        tomorrow_start = tomorrow_start_uz.astimezone(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")

        async with self.get_connection() as conn:
            async with conn.execute(
                "SELECT COUNT(*) FROM download_stats WHERE user_id = ? AND datetime(created_at) >= datetime(?) AND datetime(created_at) < datetime(?)",
                (user_id, today_start, tomorrow_start),
            ) as cursor:
                row = await cursor.fetchone()
                return row[0]

    async def log_action(self, action, user_id, details=None):
        async with self.get_connection() as conn:
            await conn.execute("INSERT INTO bot_logs (action, user_id, details, created_at) VALUES (?, ?, ?, ?)",
                           (action, user_id, details, datetime.now(timezone.utc).replace(tzinfo=None).isoformat(timespec="seconds")))
            await conn.commit()

    async def get_all_logs(self):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM bot_logs ORDER BY created_at DESC") as cursor:
                return await cursor.fetchall()

    async def add_channel(self, link):
        async with self.get_connection() as conn:
            try:
                await conn.execute("INSERT INTO channels (link) VALUES (?)", (link,))
                await conn.commit()
                return True
            except aiosqlite.IntegrityError:
                return False

    async def delete_channel(self, channel_id):
        async with self.get_connection() as conn:
            await conn.execute("DELETE FROM channels WHERE id = ?", (channel_id,))
            await conn.commit()

    async def get_channels(self):
        async with self.get_connection() as conn:
            async with conn.execute("SELECT * FROM channels") as cursor:
                return await cursor.fetchall()

    async def set_setting(self, key, value):
        """Sozlamani o'rnatadi yoki yangilaydi."""
        async with self.get_connection() as conn:
            await conn.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", (key, value))
            await conn.commit()

    async def get_setting(self, key):
        """Sozlamani olish."""
        async with self.get_connection() as conn:
            async with conn.execute("SELECT value FROM bot_settings WHERE key = ?", (key,)) as cursor:
                result = await cursor.fetchone()
            return result[0] if result else None

    async def delete_setting(self, key):
        """Sozlamani o'chirish."""
        async with self.get_connection() as conn:
            cursor = await conn.execute("DELETE FROM bot_settings WHERE key = ?", (key,))
            await conn.commit()
            return cursor.rowcount > 0

    async def get_cached_media(self, url_id, quality=None):
        """Keshdan media faylni olish"""
        async with self.get_connection() as conn:
            query = "SELECT file_id, media_type, title FROM media_cache WHERE url_id = ?"
            params = [url_id]
            if quality:
                query += " AND quality = ?"
                params.append(quality)
            async with conn.execute(query, params) as cursor:
                return await cursor.fetchone()

    async def save_cached_media(self, url_id, file_id, media_type, quality=None, file_size=0, title=None):
        """Media faylni keshga saqlash"""
        async with self.get_connection() as conn:
            await conn.execute("""
                INSERT OR REPLACE INTO media_cache (url_id, file_id, media_type, quality, file_size, title)
                VALUES (?, ?, ?, ?, ?, ?)
            """, (url_id, file_id, media_type, quality, file_size, title))
            await conn.commit()

