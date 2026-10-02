# Quick Reference: Critical Issues by Line Numbers

## CRITICAL ISSUES - MUST FIX FIRST

### 1. Missing instagram download function
- **Called at lines**: 5700, 5750, 5850 (global_link_handler, video_download_perform, etc.)
- **Issue**: `download_instagram_media()` is never defined
- **Fix**: Create function below line 5600
```python
async def download_instagram_media(message: Message, url: str, shortcode: str):
    # Implementation needed using instagrapi library
```

### 2. Missing YouTube download function
- **Called at lines**: 4000, 4200, 5650, 5750
- **Issue**: `_perform_youtube_download()` not fully implemented
- **Fix**: Complete implementation with proper signature:
```python
async def _perform_youtube_download(message: Message, video_id: str, user_id: int, bot: Bot, resolution: str = "720", callback: CallbackQuery = None, hide_title: bool = False, is_shorts: bool = False):
```

### 3. Missing music download function
- **Called at lines**: 2900, 3100, 3200
- **Issue**: `_perform_music_download()` incomplete
- **Fix**: Implement full download with yt-dlp integration

### 4. Missing show_music_page function
- **Called at line**: 2850
- **Issue**: Function displays music search pagination
- **Fix**: Implement pagination display:
```python
async def show_music_page(message: Message, results: List[Dict], page: int, lang: str):
```

### 5. Missing Facebook download function
- **Called at line**: 5800
- **Issue**: `_perform_generic_video_download()` not implemented
- **Fix**: Implement for Facebook/other video sources

---

## HIGH PRIORITY ISSUES

### Issue 8: Unreachable code after exception
**Line**: 4210-4250
```python
# PROBLEM: This code is after 'raise' - unreachable
if os.path.exists(filename) and os.path.exists(filename.rsplit('.', 1)[0] + '.mp4'):
    filename = clean_path(filename.rsplit('.', 1)[0] + '.mp4')
    title = info.get('title', 'Video')
```

### Issue 9: Race condition in download limiter
**Line**: 5650, 5850
```python
# PROBLEM: DOWNLOADING_USERS.add() is not thread-safe
if user_id in DOWNLOADING_USERS:
    return
DOWNLOADING_USERS.add(user_id)
```
**Fix**: Use asyncio.Lock instead

### Issue 10: Instagram cookies not used
**Line**: 850 (defined) - never used in download functions
```python
INSTAGRAM_COOKIES_PATH = os.path.join(BASE_DIR, "instagram_cookies.txt")  # Defined but never referenced
```

### Issue 11: Missing error cleanup
**Lines**: 3200, 3400, 5850, 5950 
```python
# PROBLEM: Files not cleaned up on exception
try:
    # ... operations
except Exception as e:
    # Missing: await safe_remove(filename)
```

### Issue 12: Session state corruption in concurrent requests
**Lines**: 6400-6500
```python
# PROBLEM: FSM state not protected by lock
current_state = await state.get_state()  # Race condition here
```

### Issue 13: Broken format string in yt-dlp
**Lines**: 4130-4140
```python
# PROBLEM: Format syntax incorrect
'postprocessor_args': {'FFmpegVideoConvertor': postprocessor_args} if postprocessor_args else None,
# Should use proper yt-dlp format codes
```

### Issue 14: No timeout on async operations
**Lines**: 3100-3200, 4000-4100
```python
# PROBLEM: Can hang indefinitely
info = await loop.run_in_executor(None, lambda: ydl.extract_info(url, download=True))
# FIX: Add timeout
info = await asyncio.wait_for(
    loop.run_in_executor(None, lambda: ydl.extract_info(url, download=True)),
    timeout=600.0
)
```

### Issue 15: Missing input validation
**Lines**: 7800-8100 (phone, location handlers)
```python
# PROBLEM: No proper validation
if message.contact:
    phone = message.contact.phone_number
else:
    phone = message.text.strip()
# Phone validation is weak, can allow invalid formats
```

### Issue 16: Memory leak in progress hooks
**Lines**: 1500-1700
```python
# PROBLEM: last_update_time list holds reference
last_update_time = [time.time()]  # This persists in memory
# Should clean up after use or use WeakRef
```

### Issue 17: Missing Shazam exception handling
**Lines**: 3100-3200
```python
# PROBLEM: Shazam errors not caught
shazam = Shazam()
out = await shazam.recognize(file_path)  # Can fail with various exceptions
# Need: except ShazamError as e:
```

### Issue 18: Unhandled Telegram API errors
**Lines**: 8500-8700 (broadcast)
```python
# PROBLEM: Only catches TelegramForbiddenError and TelegramBadRequest
for user_id in users:
    try:
        await message.copy_to(chat_id=user_id)
    except TelegramForbiddenError:  # Missing other error types
        pass
```

---

## MEDIUM PRIORITY ISSUES

### Issue 20: Incomplete compression fallback
**Lines**: 4180-4220
```python
# Only handles one case, need complete chain:
# 1. Try original format
# 2. Reduce resolution
# 3. Reduce bitrate
# 4. Convert to different codec
```

### Issue 22: Sequential user processing in broadcast
**Lines**: 8500-8700
```python
# Current: Sequential loop
for i, user in enumerate(users):
    await message.copy_to(user_id)

# FIX: Use concurrent tasks
tasks = []
for user in users:
    task = message.copy_to(user_id)
    tasks.append(task)
results = await asyncio.gather(*tasks, return_exceptions=True)
```

### Issue 23: No language fallback
**Lines**: 700-750
```python
async def get_user_lang(user_id: int) -> str:
    user = await db.get_user(user_id)
    if user and len(user) > 15 and user[15] is not None:
        return user[15]
    return 'uz'  # But doesn't validate if language is valid
    # FIX: Validate language is in TRANSLATIONS
    return user[15] if user[15] in ['uz', 'ru', 'en'] else 'uz'
```

### Issue 27: No concurrent download limit for videos
**Lines**: 5500-5700
```python
# PROBLEM: DOWNLOADING_USERS is just a set, no true limit
DOWNLOADING_USERS = set()  # Could grow indefinitely
# FIX: Use semaphore like for music downloads
video_semaphore = asyncio.Semaphore(3)  # Max 3 concurrent video downloads
```

### Issue 28: Incomplete state cleanup in error paths
**Lines**: 3200, 4300, 5600, 6800
```python
# Many handlers missing this:
except Exception as e:
    # ... error handling
    # MISSING: await clear_state_preserve_session(state)
```

### Issue 29: Missing callback.answer() in handlers
**Lines**: ~7500, ~8000, ~8200
```python
# PROBLEM: Telegram shows loading animation indefinitely
async def some_handler(callback: CallbackQuery):
    # ... process
    # MISSING: await callback.answer()
```

### Issue 30: Inconsistent admin permission checks
**Lines**: 8300-8700
```python
# Some checks missing @handlers:
@router.callback_query(F.data == "admin_panel")
async def admin_panel_handler(callback: CallbackQuery):
    if not await is_user_admin(callback.from_user.id):  # ✓ Correct
        return

@router.callback_query(F.data == "admin_orders")  # ✗ Missing check at handler level
async def orders_handler(callback: CallbackQuery, state: FSMContext):
    await clear_state_preserve_session(state)
    await show_admin_orders(callback, state, page=0)  # Check only in show_admin_orders
```

---

## LOW PRIORITY ISSUES

### Issue 38: Unused variable
**Line**: 900
```python
USERBOT_SESSION_NEEDS_RESET = False  # Defined but never used
```

### Issue 43: Magic numbers
**Lines**: 1300, 2500, 4100, 8500
```python
# Line 1300: if len(timestamps) > 5:  # What is 5?
# Line 2500: ITEMS_PER_PAGE = 10  # Should be constant
# Line 4100: 2 * 1024 * 1024 * 1024  # 2GB - should be constant
# Line 8500: ITEMS_PER_PAGE = 5  # Inconsistent with other pages

# FIX: Add at top
CAPTCHA_RATE_LIMIT = 5
MUSIC_SEARCH_PAGE_SIZE = 10
USERS_PAGE_SIZE = 10
VIDEO_SIZE_LIMIT_2GB = 2 * 1024 * 1024 * 1024
```

### Issue 44: No .env validation on startup
**Lines**: ~100 (after load_dotenv)
```python
# FIX: Add validation function
def validate_env():
    required = ['TELEGRAM_BOT_TOKEN', 'API_ID', 'API_HASH', 'ADMIN_IDS']
    for var in required:
        if not os.getenv(var):
            raise ValueError(f"Missing required .env variable: {var}")
# Call in main():
validate_env()
```

### Issue 45: Unused imports
**Lines**: Import section needs cleanup
- Check if all imported modules are used
- Remove unused ones

---

## TRANSLATION KEYS TO ADD

Review TRANSLATIONS dictionary for missing keys:
- Check all `get_text()` calls
- Verify keys exist in uz, ru, en
- Example missing (if any):
  - "some_error_message"
  - "some_feature_text"

---

## PERFORMANCE OPTIMIZATION CHECKLIST

- [ ] Add database query pagination
- [ ] Cache frequently accessed data
- [ ] Use connection pooling for database
- [ ] Implement rate limiting for expensive operations
- [ ] Add CDN for media files
- [ ] Batch database operations
- [ ] Use async context managers everywhere
- [ ] Profile code for bottlenecks

---

## TESTING CHECKLIST

- [ ] Test Instagram download with various URLs
- [ ] Test YouTube with 360p, 720p, 1080p
- [ ] Test file cleanup on errors
- [ ] Test concurrent downloads
- [ ] Test user blocking/unblocking
- [ ] Test profile creation validation
- [ ] Test CAPTCHA rate limiting
- [ ] Test language switching
- [ ] Test admin panel access control
- [ ] Test broadcast to many users

