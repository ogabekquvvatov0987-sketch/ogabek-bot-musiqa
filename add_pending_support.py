import sqlite3

conn = sqlite3.connect('bot.db')
cursor = conn.cursor()

try:
    cursor.execute("ALTER TABLE users ADD COLUMN pending_support INTEGER DEFAULT 0")
    conn.commit()
    print("pending_support ustuni muvaffaqiyatli qo‘shildi ✅")
except sqlite3.OperationalError as e:
    print("Xato:", e)

conn.close()
