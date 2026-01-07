from kivymd.app import MDApp
from kivymd.uix.button import MDRaisedButton
from kivymd.uix.screen import MDScreen
from kivymd.uix.boxlayout import MDBoxLayout
from kivymd.uix.slider import MDSlider
from kivymd.uix.label import MDLabel
from kivymd.uix.menu import MDDropdownMenu
from kivymd.uix.dialog import MDDialog
from kivymd.uix.textfield import MDTextField
from kivymd.uix.list import OneLineListItem
from kivymd.toast import toast
import threading
import time
import hashlib
import logging
from datetime import datetime
import os

# Android imports - الترتيب الصحيح مهم
from jnius import autoclass, cast, JavaException, PythonJavaClass, java_method
from android import config
from android.runnable import run_on_ui_thread

# Image processing and OCR
from PIL import Image
import pytesseract
import numpy as np
import cv2

# Translation and Arabic text handling
from deep_translator import GoogleTranslator
import arabic_reshaper
from bidi.algorithm import get_display

# ==================== Android Java Classes ====================
PythonActivity = autoclass('org.kivy.android.PythonActivity')
Intent = autoclass('android.content.Intent')
Context = autoclass('android.content.Context')
WindowManager = autoclass('android.view.WindowManager')
LayoutParams = autoclass('android.view.WindowManager$LayoutParams')
Gravity = autoclass('android.view.Gravity')
Color = autoclass('android.graphics.Color')
TextView = autoclass('android.widget.TextView')
ScrollView = autoclass('android.widget.ScrollView')
ImageReader = autoclass('android.media.ImageReader')
PixelFormat = autoclass('android.graphics.PixelFormat')
Handler = autoclass('android.os.Handler')
Looper = autoclass('android.os.Looper')
Settings = autoclass('android.provider.Settings')
Uri = autoclass('android.net.Uri')
Activity = autoclass('android.app.Activity')
NotificationManager = autoclass('android.app.NotificationManager')
NotificationChannel = autoclass('android.app.NotificationChannel')
Notification = autoclass('android.app.Notification')
Vibrator = autoclass('android.os.Vibrator')
ClipboardManager = autoclass('android.content.ClipboardManager')
ClipData = autoclass('android.content.ClipData')
Build = autoclass('android.os.Build')
PowerManager = autoclass('android.os.PowerManager')
WakeLock = autoclass('android.os.PowerManager$WakeLock')
View = autoclass('android.view.View')
Toast = autoclass('android.widget.Toast')

# ==================== Setup Logging ====================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(_name_)

# ==================== Permission Request Handler ====================
class PermissionResultHandler(PythonJavaClass):
    _javacontext_ = 'app'
    _javainterfaces_ = ['org/kivy/android/PermissionRequestListener']
    
    def __init__(self, app_instance):
        super().__init__()
        self.app = app_instance
    
    @java_method('(I[Ljava/lang/String;[I)V')
    def onRequestPermissionsResult(self, request_code, permissions, grant_results):
        logger.info(f"Permission result: request_code={request_code}")
        if request_code == 100 and len(grant_results) > 0 and grant_results[0] == 0:
            self.app.on_permission_granted(request_code)
        else:
            self.app.on_permission_denied(request_code)

# ==================== Activity Result Handler ====================
class ActivityResultCallback(PythonJavaClass):
    _javacontext_ = 'app'
    _javainterfaces_ = ['org/kivy/android/ActivityResultListener']
    
    def __init__(self, app_instance):
        super().__init__()
        self.app = app_instance
    
    @java_method('(IILandroid/content/Intent;)V')
    def onActivityResult(self, request_code, result_code, data):
        logger.info(f"Activity result: request={request_code}, result={result_code}")
        self.app.handle_activity_result(request_code, result_code, data)

# ==================== Overlay Click Listener ====================
class OverlayClickListener(PythonJavaClass):
    _javacontext_ = 'app'
    _javainterfaces_ = ['android/view/View$OnClickListener']
    
    def __init__(self, app_instance):
        super().__init__()
        self.app = app_instance
    
    @java_method('(Landroid/view/View;)V')
    def onClick(self, view):
        text = view.getText().toString()
        if text and text.strip():
            self.app.copy_to_clipboard(text)

# ==================== Translation Cache ====================
class TranslationCache:
    """Cache manager for translations with LRU eviction"""
    def __init__(self, max_size=200):
        self.cache = {}
        self.order = []  # For LRU tracking
        self.max_size = max_size
        self.hits = 0
        self.misses = 0
    
    def get(self, text):
        text_hash = self._hash_text(text)
        if text_hash in self.cache:
            # Move to end (most recently used)
            self.order.remove(text_hash)
            self.order.append(text_hash)
            self.hits += 1
            return self.cache[text_hash]['translation']
        self.misses += 1
        return None
    
    def set(self, text, translation, source_lang='auto', target_lang='arabic'):
        text_hash = self._hash_text(text)
        
        if text_hash in self.cache:
            self.order.remove(text_hash)
        elif len(self.cache) >= self.max_size:
            # Remove least recently used
            lru_hash = self.order.pop(0)
            del self.cache[lru_hash]
        
        self.cache[text_hash] = {
            'translation': translation,
            'source_lang': source_lang,
            'target_lang': target_lang,
            'timestamp': time.time()
        }
        self.order.append(text_hash)
    
    def _hash_text(self, text):
        return hashlib.md5(text.encode('utf-8')).hexdigest()
    
    def clear(self):
        self.cache.clear()
        self.order.clear()
        self.hits = 0
        self.misses = 0
    
    def stats(self):
        total = self.hits + self.misses
        hit_rate = (self.hits / total * 100) if total > 0 else 0
        return {
            'size': len(self.cache),
            'hits': self.hits,
            'misses': self.misses,
            'hit_rate': hit_rate
        }

# ==================== Main Application ====================
class ScreenTranslatorApp(MDApp):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        
        # State management
        self.service_active = False
        self.last_hash = ""
        self.translation_cache = TranslationCache(max_size=200)
        
        # Android resources
        self.overlay_view = None
        self.scroll_view = None
        self.image_reader = None
        self.projection = None
        self.virtual_display = None
        self.wm = None
        self.wake_lock = None
        
        # Translators
        self.translator = None
        self.current_target_lang = 'ar'  # Arabic code
        self.current_source_lang = 'auto'
        
        # Performance settings
        self.capture_interval = 1.5  # seconds
        self.capture_resolution = (0.6, 0.6)  # width, height scale
        self.text_min_length = 10  # Minimum text length to process
        
        # UI settings
        self.font_size = 18
        self.max_overlay_lines = 10
        
        # Threading
        self.processing_thread = None
        self.processing_active = False
        
        # Error handling
        self.error_count = 0
        self.max_errors = 5
        
        # Handlers
        self.permission_handler = None
        self.activity_result_handler = None
        
        # History
        self.translation_history = []
        self.max_history_size = 100
        
        # Supported languages
        self.supported_languages = {
            'ar': 'العربية',
            'en': 'الإنجليزية',
            'fr': 'الفرنسية',
            'es': 'الإسبانية',
            'de': 'الألمانية',
            'ru': 'الروسية',
            'zh': 'الصينية',
            'ja': 'اليابانية',
            'ko': 'الكورية',
            'tr': 'التركية',
            'fa': 'الفارسية',
            'ur': 'الأردية'
        }
        
        # Configure pytesseract
        pytesseract.pytesseract.tesseract_cmd = '/usr/bin/tesseract'  # Default path
    
    def build(self):
        self.theme_cls.primary_palette = "Indigo"
        self.theme_cls.theme_style = "Dark"
        
        # Main layout
        layout = MDBoxLayout(orientation='vertical', padding=20, spacing=15)
        
        # Title
        title = MDLabel(
            text="مترجم الشاشة الذكي",
            halign="center",
            font_style="H4",
            theme_text_color="Primary",
            size_hint_y=None,
            height=50
        )
        layout.add_widget(title)
        
        # Status label
        self.status_label = MDLabel(
            text="جاهز للبدء",
            halign="center",
            theme_text_color="Secondary",
            size_hint_y=None,
            height=30
        )
        layout.add_widget(self.status_label)
        
        # Control button
        self.control_btn = MDRaisedButton(
            text="بدء الخدمة",
            pos_hint={'center_x': 0.5},
            on_release=self.toggle_service,
            size_hint=(0.8, None),
            height=50
        )
        layout.add_widget(self.control_btn)
        
        # Settings button
        settings_btn = MDRaisedButton(
            text="الإعدادات",
            pos_hint={'center_x': 0.5},
            on_release=self.open_settings_dialog,
            size_hint=(0.6, None),
            height=45
        )
        layout.add_widget(settings_btn)
        
        # Performance info
        self.performance_label = MDLabel(
            text="",
            halign="center",
            theme_text_color="Hint",
            font_style="Caption",
            size_hint_y=None,
            height=25
        )
        layout.add_widget(self.performance_label)
        
        screen = MDScreen()
        screen.add_widget(layout)
        return screen
    
    def on_start(self):
        """Initialize when app starts"""
        # Register activity result handler
        self.activity_result_handler = ActivityResultCallback(self)
        activity = PythonActivity.mActivity
        activity.addActivityResultListener(self.activity_result_handler)
        
        # Update UI
        self.update_performance_info()
    
    def on_stop(self):
        """Cleanup when app stops"""
        self.stop_service()
        
        # Remove listeners
        if self.activity_result_handler:
            activity = PythonActivity.mActivity
            activity.removeActivityResultListener(self.activity_result_handler)
        
        super().on_stop()
    
    # ==================== Service Control ====================
    def toggle_service(self, *args):
        """Toggle service on/off"""
        if self.service_active:
            self.stop_service()
        else:
            self.start_service()
    
    def start_service(self):
        """Start the translation service"""
        if self.service_active:
            self.show_android_toast("الخدمة تعمل بالفعل")
            return
        
        self.check_permissions()
    
    def stop_service(self):
        """Stop the translation service"""
        if not self.service_active:
            return
        
        logger.info("Stopping service...")
        self.service_active = False
        self.processing_active = False
        
        # Wait for processing thread to finish
        if self.processing_thread and self.processing_thread.is_alive():
            self.processing_thread.join(timeout=3.0)
        
        # Cleanup resources
        self.cleanup_resources()
        
        # Update UI
        self.control_btn.text = "بدء الخدمة"
        self.status_label.text = "متوقف"
        self.show_android_toast("تم إيقاف الخدمة")
        
        logger.info("Service stopped")
    
    # ==================== Permissions ====================
    def check_permissions(self):
        """Check and request necessary permissions"""
        activity = PythonActivity.mActivity
        
        # Check overlay permission for Android 6.0+
        if Build.VERSION.SDK_INT >= 23:
            if not Settings.canDrawOverlays(activity):
                self.request_overlay_permission()
                return
        
        # Request screen capture permission
        self.request_screen_capture()
    
    def request_overlay_permission(self):
        """Request overlay/draw over other apps permission"""
        self.status_label.text = "يطلب صلاحية النافذة العائمة"
        
        activity = PythonActivity.mActivity
        intent = Intent(
            Settings.ACTION_MANAGE_OVERLAY_PERMISSION,
            Uri.parse("package:" + activity.getPackageName())
        )
        activity.startActivityForResult(intent, 101)
    
    def request_screen_capture(self):
        """Request screen capture permission"""
        self.status_label.text = "يطلب صلاحية التقاط الشاشة"
        
        activity = PythonActivity.mActivity
        media_proj = activity.getSystemService(Context.MEDIA_PROJECTION_SERVICE)
        intent = media_proj.createScreenCaptureIntent()
        activity.startActivityForResult(intent, 102)
    
    def handle_activity_result(self, request_code, result_code, data):
        """Handle activity result from permission requests"""
        logger.info(f"Handling activity result: {request_code}, {result_code}")
        
        if result_code != Activity.RESULT_OK:
            self.status_label.text = "تم رفض الصلاحية"
            self.show_android_toast("يجب منح الصلاحية لتشغيل التطبيق")
            return
        
        if request_code == 101:  # Overlay permission granted
            self.status_label.text = "تم منح صلاحية النافذة"
            # Request screen capture after overlay permission
            time.sleep(0.5)
            self.request_screen_capture()
        
        elif request_code == 102:  # Screen capture permission granted
            self.setup_and_start_service(result_code, data)
    
    def on_permission_granted(self, request_code):
        """Handle granted permission (for runtime permissions)"""
        logger.info(f"Permission granted: {request_code}")
    
    def on_permission_denied(self, request_code):
        """Handle denied permission"""
        logger.warning(f"Permission denied: {request_code}")
        self.show_android_toast("يجب منح جميع الصلاحيات")
    
    # ==================== Service Setup ====================
    def setup_and_start_service(self, result_code, data):
        """Setup and start service after permissions granted"""
        try:
            # Initialize translator
            self.translator = GoogleTranslator(
                source=self.current_source_lang,
                target=self.current_target_lang
            )
            
            # Create overlay UI
            self.create_overlay_ui()
            
            # Setup screen capture
            self.setup_screen_capture(result_code, data)
            
            # Acquire wake lock to keep CPU running
            self.acquire_wake_lock()
            
            # Start processing thread
            self.service_active = True
            self.processing_active = True
            self.processing_thread = threading.Thread(
                target=self.processing_loop,
                daemon=True,
                name="ScreenTranslationProcessor"
            )
            self.processing_thread.start()
            
            # Update UI
            self.control_btn.text = "إيقاف الخدمة"
            self.status_label.text = "الخدمة تعمل..."
            self.show_android_toast("بدأت الخدمة بنجاح")
            
            logger.info("Service setup completed successfully")
            
        except Exception as e:
            logger.error(f"Failed to setup service: {e}")
            self.status_label.text = "فشل بدء الخدمة"
            self.show_android_toast(f"خطأ في الإعداد: {str(e)}")
            self.cleanup_resources()
    
    @run_on_ui_thread
    def create_overlay_ui(self):
        """Create overlay UI on Android window"""
        try:
            activity = PythonActivity.mActivity
            self.wm = cast(WindowManager, activity.getSystemService(Context.WINDOW_SERVICE))
            
            # Create ScrollView
            self.scroll_view = ScrollView(activity)
            self.scroll_view.setLayoutParams(android_widget.AbsoluteLayout.LayoutParams(
                LayoutParams.MATCH_PARENT,
                LayoutParams.WRAP_CONTENT
            ))
            
            # Create TextView
            self.overlay_view = TextView(activity)
            self.overlay_view.setTextColor(Color.YELLOW)
            self.overlay_view.setBackgroundColor(Color.argb(180, 0, 0, 0))  # Semi-transparent
            self.overlay_view.setTextSize(self.font_size)
            self.overlay_view.setPadding(25, 15, 25, 15)
            self.overlay_view.setLineSpacing(1.1, 1.1)
            self.overlay_view.setMaxLines(self.max_overlay_lines)
            self.overlay_view.setEllipsize(android_text.TextUtils.TruncateAt.END)
            
            # Set click listener
            click_listener = OverlayClickListener(self)
            self.overlay_view.setOnClickListener(click_listener)
            
            # Add TextView to ScrollView
            self.scroll_view.addView(self.overlay_view)
            
            # Create layout parameters
            params = LayoutParams()
            params.width = LayoutParams.MATCH_PARENT
            params.height = LayoutParams.WRAP_CONTENT
            
            # Set type based on Android version
            if Build.VERSION.SDK_INT >= 26:
                params.type = LayoutParams.TYPE_APPLICATION_OVERLAY
            else:
                params.type = LayoutParams.TYPE_PHONE
            
            params.flags = (
                LayoutParams.FLAG_NOT_FOCUSABLE |
                LayoutParams.FLAG_NOT_TOUCH_MODAL |
                LayoutParams.FLAG_WATCH_OUTSIDE_TOUCH |
                LayoutParams.FLAG_LAYOUT_NO_LIMITS
            )
            params.format = PixelFormat.TRANSLUCENT
            params.gravity = Gravity.TOP | Gravity.CENTER_HORIZONTAL
            
            # Add view to window manager
            self.wm.addView(self.scroll_view, params)
            
            logger.info("Overlay UI created successfully")
            
        except Exception as e:
            logger.error(f"Failed to create overlay UI: {e}")
            raise
    
    def setup_screen_capture(self, result_code, data):
        """Setup screen capture with proper resolution"""
        try:
            activity = PythonActivity.mActivity
            
            # Get display metrics
            metrics = activity.getResources().getDisplayMetrics()
            original_width = metrics.widthPixels
            original_height = metrics.heightPixels
            density = metrics.densityDpi
            
            # Calculate capture dimensions
            capture_width = int(original_width * self.capture_resolution[0])
            capture_height = int(original_height * self.capture_resolution[1])
            
            # Ensure minimum dimensions
            capture_width = max(capture_width, 480)
            capture_height = max(capture_height, 320)
            
            logger.info(f"Capture dimensions: {capture_width}x{capture_height}")
            
            # Create ImageReader
            self.image_reader = ImageReader.newInstance(
                capture_width,
                capture_height,
                PixelFormat.RGBA_8888,
                2  # Max images to keep in buffer
            )
            
            # Get media projection
            media_proj_service = activity.getSystemService(Context.MEDIA_PROJECTION_SERVICE)
            self.projection = media_proj_service.getMediaProjection(result_code, data)
            
            # Create virtual display
            self.virtual_display = self.projection.createVirtualDisplay(
                "ScreenTranslatorDisplay",
                capture_width,
                capture_height,
                density,
                16,  # VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR
                self.image_reader.getSurface(),
                None,
                None
            )
            
            logger.info("Screen capture setup completed")
            
        except Exception as e:
            logger.error(f"Failed to setup screen capture: {e}")
            raise
    
    def acquire_wake_lock(self):
        """Acquire wake lock to prevent CPU sleep"""
        try:
            activity = PythonActivity.mActivity
            power_manager = cast(PowerManager, activity.getSystemService(Context.POWER_SERVICE))
            self.wake_lock = power_manager.newWakeLock(
                PowerManager.PARTIAL_WAKE_LOCK,
                "ScreenTranslator::WakeLock"
            )
            self.wake_lock.acquire()
            logger.info("Wake lock acquired")
        except Exception as e:
            logger.warning(f"Could not acquire wake lock: {e}")
    
    # ==================== Main Processing Loop ====================
    def processing_loop(self):
        """Main processing loop for screen capture and translation"""
        logger.info("Processing loop started")
        
        frames_processed = 0
        last_text_hash = ""
        last_process_time = 0
        
        while self.processing_active and self.error_count < self.max_errors:
            try:
                current_time = time.time()
                
                # Calculate dynamic sleep time
                time_since_last = current_time - last_process_time
                if time_since_last < self.capture_interval:
                    sleep_time = self.capture_interval - time_since_last
                    time.sleep(max(0.1, sleep_time))
                    continue
                
                # Acquire latest image
                image = self.image_reader.acquireLatestImage()
                if not image:
                    time.sleep(0.05)
                    continue
                
                # Process image and extract text
                start_process = time.time()
                extracted_text = self.process_image(image)
                image.close()
                
                # Check if we have valid text
                if extracted_text and len(extracted_text.strip()) >= self.text_min_length:
                    current_hash = hashlib.md5(extracted_text.encode('utf-8')).hexdigest()
                    
                    # Only process if text has changed
                    if current_hash != last_text_hash:
                        last_text_hash = current_hash
                        
                        # Translate text
                        translated_text = self.translate_text(extracted_text)
                        
                        if translated_text:
                            # Update overlay with translated text
                            self.update_overlay_text(translated_text)
                            
                            # Add to history
                            self.add_to_history(extracted_text, translated_text)
                            
                            # Update performance info occasionally
                            if frames_processed % 10 == 0:
                                self.update_performance_info()
                
                # Update timing
                frames_processed += 1
                last_process_time = time.time()
                process_duration = last_process_time - start_process
                
                # Adaptive interval adjustment
                if process_duration > self.capture_interval * 1.2:
                    # Slow down if processing is taking too long
                    self.capture_interval = min(3.0, self.capture_interval * 1.1)
                elif process_duration < self.capture_interval * 0.8:
                    # Speed up if we have extra capacity
                    self.capture_interval = max(0.8, self.capture_interval * 0.9)
                
                # Reset error count on success
                self.error_count = 0
                
            except Exception as e:
                self.error_count += 1
                logger.error(f"Error in processing loop ({self.error_count}/{self.max_errors}): {e}")
                
                if self.error_count >= self.max_errors:
                    logger.critical("Too many errors, stopping service")
                    self.show_android_toast("توقف الخدمة بسبب أخطاء متعددة")
                    self.stop_service()
                else:
                    time.sleep(2.0)  # Wait before retrying
        
        logger.info(f"Processing loop ended. Frames processed: {frames_processed}")
    
    def process_image(self, image):
        """Process Android Image and extract text using OCR"""
        try:
            # Get image dimensions
            width = image.getWidth()
            height = image.getHeight()
            
            # Get the first plane (should be RGBA)
            plane = image.getPlanes()[0]
            buffer = plane.getBuffer()
            
            # Create byte array
            pixel_data = bytearray(buffer.remaining())
            buffer.get(pixel_data)
            
            # Convert to numpy array and reshape
            img_array = np.frombuffer(pixel_data, dtype=np.uint8).reshape((height, width, 4))
            
            # Convert RGBA to RGB for PIL
            rgb_array = cv2.cvtColor(img_array, cv2.COLOR_RGBA2RGB)
            
            # Create PIL Image
            pil_image = Image.fromarray(rgb_array)
            
            # Preprocess for better OCR
            processed_image = self.preprocess_image(pil_image)
            
            # Perform OCR with multiple languages
            config = '--oem 3 --psm 3'
            text = pytesseract.image_to_string(
                processed_image,
                lang='eng+ara',  # English and Arabic
                config=config
            ).strip()
            
            # Clean up
            del img_array, rgb_array, pixel_data
            
            return text
            
        except Exception as e:
            logger.error(f"Image processing error: {e}")
            return ""
    
    def preprocess_image(self, image):
        """Preprocess image for better OCR results"""
        try:
            # Convert to grayscale
            gray = image.convert('L')
            
            # Resize for better performance while maintaining quality
            if self.capture_resolution[0] < 0.8:
                scale_factor = 1.5
                new_width = int(gray.width * scale_factor)
                new_height = int(gray.height * scale_factor)
                gray = gray.resize((new_width, new_height), Image.Resampling.LANCZOS)
            
            # Apply contrast enhancement
            from PIL import ImageEnhance
            enhancer = ImageEnhance.Contrast(gray)
            gray = enhancer.enhance(1.5)  # Increase contrast by 50%
            
            # Optional: Apply thresholding for binary image
            # gray = gray.point(lambda x: 0 if x < 180 else 255, '1')
            
            return gray
            
        except Exception as e:
            logger.warning(f"Image preprocessing error, using original: {e}")
            return image.convert('L')
    
    def translate_text(self, text):
        """Translate text with caching"""
        try:
            # Check cache first
            cached = self.translation_cache.get(text)
            if cached:
                return cached
            
            # Check if text is already in target language (simple check)
            if self.current_target_lang == 'ar' and self.is_arabic(text):
                return text  # Already Arabic
            
            # Perform translation
            translated = self.translator.translate(text)
            
            # Reshape Arabic text for proper display
            if self.current_target_lang == 'ar':
                translated = self.reshape_arabic_text(translated)
            
            # Cache the result
            self.translation_cache.set(
                text, 
                translated, 
                self.current_source_lang, 
                self.current_target_lang
            )
            
            return translated
            
        except Exception as e:
            logger.error(f"Translation error: {e}")
            return f"[خطأ في الترجمة]"
    
    def is_arabic(self, text):
        """Check if text contains Arabic characters"""
        arabic_range = range(0x0600, 0x06FF + 1)
        for char in text:
            if ord(char) in arabic_range:
                return True
        return False
    
    def reshape_arabic_text(self, text):
        """Reshape Arabic text for proper display"""
        try:
            reshaped = arabic_reshaper.reshape(text)
            return get_display(reshaped)
        except:
            return text
    
    @run_on_ui_thread
    def update_overlay_text(self, text):
        """Update overlay text on UI thread"""
        if self.overlay_view and text:
            self.overlay_view.setText(text)
            
            # Vibrate briefly for new translation
            try:
                activity = PythonActivity.mActivity
                vibrator = activity.getSystemService(Context.VIBRATOR_SERVICE)
                if vibrator and vibrator.hasVibrator():
                    vibrator.vibrate(50)  # 50ms vibration
            except:
                pass
    
    def add_to_history(self, original, translated):
        """Add translation to history"""
        entry = {
            'timestamp': datetime.now().strftime("%H:%M:%S"),
            'original': original[:100] + "..." if len(original) > 100 else original,
            'translated': translated[:100] + "..." if len(translated) > 100 else translated,
            'full_original': original,
            'full_translated': translated
        }
        
        self.translation_history.insert(0, entry)
        
        # Limit history size
        if len(self.translation_history) > self.max_history_size:
            self.translation_history = self.translation_history[:self.max_history_size]
    
    # ==================== UI Methods ====================
    def update_performance_info(self):
        """Update performance information display"""
        cache_stats = self.translation_cache.stats()
        info = f"ذاكرة التخزين: {cache_stats['size']} | نجاح: {cache_stats['hit_rate']:.1f}%"
        self.performance_label.text = info
    
    def open_settings_dialog(self, *args):
        """Open settings dialog"""
        content = MDBoxLayout(
            orientation='vertical',
            spacing='10dp',
            size_hint_y=None,
            height='350dp'
        )
        
        # Target language selection
        lang_label = MDLabel(
            text="لغة الترجمة:",
            size_hint_y=None,
            height='30dp'
        )
        content.add_widget(lang_label)
        
        # Add more settings as needed...
        
        dialog = MDDialog(
            title="الإعدادات",
            type="custom",
            content_cls=content,
            buttons=[
                MDRaisedButton(
                    text="حفظ",
                    on_release=lambda x: self.save_settings(dialog)
                ),
                MDRaisedButton(
                    text="إلغاء",
                    on_release=lambda x: dialog.dismiss()
                )
            ]
        )
        dialog.open()
    
    def save_settings(self, dialog):
        """Save settings"""
        dialog.dismiss()
        self.show_android_toast("تم حفظ الإعدادات")
    
    # ==================== Utility Methods ====================
    @run_on_ui_thread
    def show_android_toast(self, message):
        """Show Android toast message"""
        try:
            activity = PythonActivity.mActivity
            toast = Toast.makeText(activity, str(message), Toast.LENGTH_SHORT)
            toast.show()
        except:
            # Fallback to Kivy toast
            toast(message)
    
    @run_on_ui_thread
    def copy_to_clipboard(self, text):
        """Copy text to Android clipboard"""
        try:
            activity = PythonActivity.mActivity
            clipboard = cast(ClipboardManager, 
                           activity.getSystemService(Context.CLIPBOARD_SERVICE))
            clip = ClipData.newPlainText("translated_text", text)
            clipboard.setPrimaryClip(clip)
            self.show_android_toast("تم نسخ النص إلى الحافظة")
        except Exception as e:
            logger.error(f"Failed to copy to clipboard: {e}")
    
    # ==================== Resource Cleanup ====================
    def cleanup_resources(self):
        """Clean up all resources properly"""
        logger.info("Starting resource cleanup")
        
        try:
            # Release wake lock
            if self.wake_lock and self.wake_lock.isHeld():
                self.wake_lock.release()
                self.wake_lock = None
                logger.info("Wake lock released")
        except Exception as e:
            logger.warning(f"Error releasing wake lock: {e}")
        
        try:
            # Remove overlay view
            if self.scroll_view and self.wm:
                self.wm.removeView(self.scroll_view)
                self.scroll_view = None
                self.overlay_view = None
                logger.info("Overlay view removed")
        except Exception as e:
            logger.warning(f"Error removing overlay: {e}")
        
        try:
            # Stop virtual display
            if self.virtual_display:
                self.virtual_display.release()
                self.virtual_display = None
                logger.info("Virtual display released")
        except Exception as e:
            logger.warning(f"Error releasing virtual display: {e}")
        
        try:
            # Stop projection
            if self.projection:
                self.projection.stop()
                self.projection = None
                logger.info("Media projection stopped")
        except Exception as e:
            logger.warning(f"Error stopping projection: {e}")
        
        try:
            # Close image reader
            if self.image_reader:
                self.image_reader.close()
                self.image_reader = None
                logger.info("Image reader closed")
        except Exception as e:
            logger.warning(f"Error closing image reader: {e}")
        
        # Clear cache
        self.translation_cache.clear()
        
        # Reset state
        self.service_active = False
        self.processing_active = False
        self.error_count = 0
        
        logger.info("Resource cleanup completed")

# ==================== Additional imports for Android widgets ====================
# Import here to avoid circular imports
android_widget = autoclass('android.widget')
android_text = autoclass('android.text')

# ==================== Main Entry Point ====================
def main():
    """Main entry point with proper exception handling"""
    try:
        # Set environment variables for Android
        os.environ['KIVY_ANDROID'] = '1'
        
        # Run the application
        app = ScreenTranslatorApp()
        app.run()
        
    except Exception as e:
        logger.critical(f"Fatal error in main: {e}", exc_info=True)
        
        # Show error to user
        try:
            activity = PythonActivity.mActivity
            toast = Toast.makeText(activity, f"خطأ في التطبيق: {str(e)[:50]}", Toast.LENGTH_LONG)
            toast.show()
        except:
            pass
        
        raise

if _name_ == "_main_":

    main()
    # start build
