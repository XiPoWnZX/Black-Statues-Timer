import json
import math
import os
import queue
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import tkinter as tk
from tkinter import messagebox, simpledialog
from pathlib import Path

try:
    import winsound
except ImportError:
    winsound = None


# ============================================================
# BLACK STATUES CHAIN TIMER
# MADE BY XIPOWNZX FOR EXCLUSIVE USE OF BLACK STATUES FACTION
# ============================================================

APP_NAME = "Black Statues Chain"
FACTION_ID = 9412

API_URL = f"https://api.torn.com/faction/{FACTION_ID}"
VERIFY_API_URL = "https://api.torn.com/v2/user/faction"

POLL_INTERVAL = 5
REQUEST_TIMEOUT = 10
STALE_AFTER_SECONDS = 20
UNCHANGED_AFTER_SECONDS = 60

NORMAL_WIDTH = 295
NORMAL_HEIGHT = 200
COMPACT_WIDTH = 180
COMPACT_HEIGHT = 110
SCREEN_MARGIN = 10

ALARM_START_SECONDS = 30
NORMAL_BEEP_FREQUENCY = 1800
NORMAL_BEEP_DURATION_MS = 350
NORMAL_BEEP_PAUSE_MS = 160
FINAL_BEEP_FREQUENCY = 2500
FINAL_BEEP_DURATION_MS = 300
FINAL_BEEP_PAUSE_MS = 40
FAILURE_BEEP_FREQUENCY = 450
FAILURE_BEEP_DURATION_MS = 3000

CONFIG_DIR = Path(os.environ.get("APPDATA", str(Path.home()))) / "TornChainTimer"
CONFIG_FILE = CONFIG_DIR / "config.json"


class ChainTimerApp:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_NAME)
        self.root.geometry(f"{NORMAL_WIDTH}x{NORMAL_HEIGHT}")
        self.root.resizable(False, False)
        self.root.attributes("-topmost", True)
        self.root.attributes("-alpha", 0.85)
        self.root.configure(bg="#151515")

        self.config = self.load_config()

        self.deadline = None
        self.last_timeout_value = None
        self._last_applied_timeout = None
        self.last_success_monotonic = None
        self.last_timeout_change_monotonic = None
        self.last_api_message = "Waiting for API connection..."

        self.polling = False
        self.poll_stop_event = threading.Event()
        self.result_queue = queue.Queue()
        self.request_lock = threading.Lock()

        self.validated_api_key = None
        self.key_validation_in_progress = False

        self.alarm_stop_event = threading.Event()
        self.alarm_thread = None
        self.alarm_lock = threading.Lock()
        self.failure_sound_played = False

        self.compact_mode = False
        self.locked = False
        self.flash_visible = True
        self.last_flash_toggle = time.monotonic()
        self.drag_x = 0
        self.drag_y = 0

        self.build_interface()
        self.root.protocol("WM_DELETE_WINDOW", self.close_app)
        self.position_top_right(NORMAL_WIDTH, NORMAL_HEIGHT)

        self.update_display()
        self.process_queue()

        # Automatically poll on launch when a saved API key exists.
        if self.config.get("api_key", "").strip():
            self.root.after(500, self.start_polling)

    # --------------------------------------------------------
    # CONFIGURATION
    # --------------------------------------------------------

    def load_config(self):
        try:
            CONFIG_DIR.mkdir(parents=True, exist_ok=True)
            if CONFIG_FILE.exists():
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    return data
        except Exception as exc:
            print("Configuration load error:", exc)
        return {"api_key": ""}

    def save_config(self):
        try:
            CONFIG_DIR.mkdir(parents=True, exist_ok=True)
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(self.config, f, indent=2)
            return True
        except Exception as exc:
            messagebox.showerror(
                "API Key Error",
                f"Could not save API key:\n{exc}",
                parent=self.root
            )
            return False

    def open_settings(self):
        if self.key_validation_in_progress:
            messagebox.showinfo(
                "API Key",
                "An API key is already being verified. Please wait.",
                parent=self.root
            )
            return

        new_key = simpledialog.askstring(
            "API Key",
            "Enter your Torn API key:\n"
            "Only keys belonging to faction 9412 are accepted.",
            initialvalue=self.config.get("api_key", ""),
            show="*",
            parent=self.root
        )

        if new_key is None:
            return

        new_key = new_key.strip()
        if not new_key:
            messagebox.showwarning(
                "API Key",
                "The API key cannot be empty.",
                parent=self.root
            )
            return

        if new_key == self.config.get("api_key", "").strip():
            self.set_message("Checking the saved API key...")
        else:
            self.set_message("Verifying API key and faction membership...")

        self.key_validation_in_progress = True
        threading.Thread(
            target=self.validate_key_worker,
            args=(new_key,),
            daemon=True
        ).start()

    # --------------------------------------------------------
    # TORN API KEY VALIDATION
    # --------------------------------------------------------

    def validate_api_key(self, api_key):
        params = urllib.parse.urlencode({
            "key": api_key,
            "timestamp": str(int(time.time()))
        })
        request = urllib.request.Request(
            f"{VERIFY_API_URL}?{params}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache"
            }
        )

        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8"))

        if not isinstance(data, dict):
            raise ValueError("Torn returned an unexpected verification response.")

        if "error" in data:
            error = data["error"]
            if isinstance(error, dict):
                raise ValueError(
                    f"Torn API error {error.get('code', '?')}: "
                    f"{error.get('error', 'Unknown error')}"
                )
            raise ValueError(str(error))

        faction = data.get("faction")
        if not isinstance(faction, dict):
            raise ValueError(
                "Torn did not return faction information for this API key. "
                "Make sure the key has access to the user → faction selection "
                "and that its owner is currently in a faction."
            )

        try:
            faction_id = int(faction.get("id"))
        except (TypeError, ValueError):
            raise ValueError("Torn returned an invalid faction ID. The key cannot be verified.")

        if faction_id != FACTION_ID:
            faction_name = faction.get("name", "Unknown faction")
            raise ValueError(
                f"This API key belongs to faction '{faction_name}' "
                f"(ID {faction_id}), not BLACK STATUES (ID {FACTION_ID}). "
                "The key was not saved."
            )

        return {"id": faction_id, "name": faction.get("name", "BLACK STATUES")}

    def validate_key_worker(self, api_key):
        try:
            faction = self.validate_api_key(api_key)
            self.result_queue.put(("key_validated", {
                "api_key": api_key,
                "faction": faction
            }))
        except urllib.error.HTTPError as exc:
            self.result_queue.put((
                "key_validation_error",
                f"HTTP error {exc.code}: {exc.reason}"
            ))
        except urllib.error.URLError as exc:
            self.result_queue.put((
                "key_validation_error",
                f"Network error while verifying the key: {exc.reason}"
            ))
        except Exception as exc:
            self.result_queue.put(("key_validation_error", str(exc)))

    def handle_key_validated(self, result):
        self.key_validation_in_progress = False
        api_key = result["api_key"]
        faction = result["faction"]

        old_key = self.config.get("api_key", "")
        self.config["api_key"] = api_key

        if not self.save_config():
            self.config["api_key"] = old_key
            self.validated_api_key = None
            return

        self.validated_api_key = api_key
        self.set_message(
            f"Verified: {faction['name']} (ID {faction['id']})."
        )

        # Start polling automatically after first-time key verification.
        if not self.polling:
            self.start_polling()
        else:
            self.refresh_api()

    def handle_key_validation_error(self, error):
        self.key_validation_in_progress = False
        self.set_message("API key verification failed.")
        messagebox.showerror(
            "API Key Rejected",
            "The API key could not be verified for BLACK STATUES.\n\n"
            f"{error}\n\n"
            "The new key was not saved.",
            parent=self.root
        )

    # --------------------------------------------------------
    # WINDOW POSITIONING
    # --------------------------------------------------------

    def position_top_right(self, width, height):
        self.root.update_idletasks()
        screen_width = self.root.winfo_screenwidth()
        x = max(0, screen_width - width - SCREEN_MARGIN)
        self.root.geometry(f"{width}x{height}+{x}+{SCREEN_MARGIN}")
        self.root.attributes("-topmost", True)

    def toggle_lock(self):
        self.locked = not self.locked
        self.update_lock_buttons()

    def update_lock_buttons(self):
        text = "🔒" if self.locked else "🔓"
        bg = "#7b3434" if self.locked else "#353944"
        active_bg = "#914444" if self.locked else "#505666"

        self.normal_lock_button.config(text=text, bg=bg, activebackground=active_bg)
        self.compact_lock_button.config(text=text, bg=bg, activebackground=active_bg)
        self.normal_lock_button.config(command=self.toggle_lock)
        self.compact_lock_button.config(command=self.toggle_lock)

    # --------------------------------------------------------
    # USER INTERFACE
    # --------------------------------------------------------

    def build_interface(self):
        bg = "#17191f"

        self.normal_frame = tk.Frame(self.root, bg=bg, padx=10, pady=5)
        self.normal_frame.pack(fill="both", expand=True)

        normal_top = tk.Frame(self.normal_frame, bg=bg)
        normal_top.pack(fill="x")

        self.title_label = tk.Label(
            normal_top, text=APP_NAME, font=("Segoe UI", 13, "bold"),
            fg="white", bg=bg, anchor="center"
        )
        self.title_label.pack(side="left", fill="x", expand=True)

        self.normal_lock_button = tk.Button(
            normal_top, text="🔓", command=self.toggle_lock,
            font=("Segoe UI Emoji", 9), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=3, padx=0, pady=0, cursor="hand2"
        )
        self.normal_lock_button.pack(side="right")

        self.timer_label = tk.Label(
            self.normal_frame, text="--:--", font=("Consolas", 32, "bold"),
            fg="#63e68b", bg=bg, anchor="center"
        )
        self.timer_label.pack(fill="x", pady=(0, 0))

        self.status_label = tk.Label(
            self.normal_frame, text="Waiting for API connection...",
            font=("Segoe UI", 8), fg="#c5c8d0", bg=bg,
            wraplength=350, justify="center", anchor="center"
        )
        self.status_label.pack(fill="x", pady=(0, 3))

        self.normal_stale_label = tk.Label(
            self.normal_frame, text="WARNING: API connection not verified",
            font=("Segoe UI", 9, "bold"), fg="#e9b44c", bg=bg,
            anchor="center", justify="center"
        )
        self.normal_stale_label.pack(fill="x")

        self.normal_unchanged_label = tk.Label(
            self.normal_frame, text="Timeout: waiting for first valid value",
            font=("Segoe UI", 9, "bold"), fg="#e9b44c", bg=bg,
            anchor="center", justify="center"
        )
        self.normal_unchanged_label.pack(fill="x", pady=(1, 4))

        button_frame = tk.Frame(self.normal_frame, bg=bg)
        button_frame.pack(fill="x", pady=(1, 0))

        buttons = [
            ("API Key", self.open_settings),
            ("Small Countdown", self.toggle_countdown_mode),
            ("Start", self.start_polling),
            ("Stop", self.stop_polling),
            ("Refresh", self.refresh_api),
        ]
        for text, command in buttons:
            tk.Button(
                button_frame, text=text, command=command,
                font=("Segoe UI", 8), fg="white", bg="#353944",
                activebackground="#505666", activeforeground="white",
                relief="flat", bd=0, padx=3, pady=4, cursor="hand2"
            ).pack(side="left", expand=True, fill="x", padx=2)

        self.compact_frame = tk.Frame(self.root, bg=bg, padx=6, pady=3)
        compact_top = tk.Frame(self.compact_frame, bg=bg)
        compact_top.pack(fill="x")

        self.compact_lock_button = tk.Button(
            compact_top, text="🔓", command=self.toggle_lock,
            font=("Segoe UI Emoji", 8), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=3, padx=0, pady=0, cursor="hand2"
        )
        self.compact_lock_button.pack(side="left")

        self.compact_title = tk.Label(
            compact_top, text=APP_NAME, font=("Segoe UI", 8, "bold"),
            fg="white", bg=bg, anchor="center"
        )
        self.compact_title.pack(side="left", fill="x", expand=True)

        self.expand_button = tk.Button(
            compact_top, text="↗", command=self.toggle_countdown_mode,
            font=("Segoe UI", 10, "bold"), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=2, padx=0, pady=0, cursor="hand2"
        )
        self.expand_button.pack(side="right")

        self.compact_timer_label = tk.Label(
            self.compact_frame, text="--:--", font=("Consolas", 21, "bold"),
            fg="#63e68b", bg=bg, anchor="center"
        )
        self.compact_timer_label.pack(fill="x", pady=(0, 0))

        self.compact_stale_label = tk.Label(
            self.compact_frame, text="WARNING: API connection not verified",
            font=("Segoe UI", 7, "bold"), fg="#e9b44c", bg=bg,
            anchor="center", justify="center"
        )
        self.compact_stale_label.pack(fill="x")

        self.compact_unchanged_label = tk.Label(
            self.compact_frame, text="Timeout: waiting for first valid value",
            font=("Segoe UI", 7, "bold"), fg="#e9b44c", bg=bg,
            anchor="center", justify="center"
        )
        self.compact_unchanged_label.pack(fill="x")

        drag_widgets = [
            self.root, self.normal_frame, normal_top, self.title_label,
            self.timer_label, self.status_label, self.normal_stale_label,
            self.normal_unchanged_label, self.compact_frame, compact_top,
            self.compact_title, self.compact_timer_label,
            self.compact_stale_label, self.compact_unchanged_label
        ]
        for widget in drag_widgets:
            widget.bind("<ButtonPress-1>", self.start_drag)
            widget.bind("<B1-Motion>", self.drag_window)

        self.update_lock_buttons()

    # --------------------------------------------------------
    # MODE SWITCHING
    # --------------------------------------------------------

    def toggle_countdown_mode(self):
        if not self.compact_mode:
            self.compact_mode = True
            self.normal_frame.pack_forget()
            self.compact_frame.pack(fill="both", expand=True)
            self.position_top_right(COMPACT_WIDTH, COMPACT_HEIGHT)
        else:
            self.compact_mode = False
            self.compact_frame.pack_forget()
            self.normal_frame.pack(fill="both", expand=True)
            self.position_top_right(NORMAL_WIDTH, NORMAL_HEIGHT)

        self.root.attributes("-topmost", True)
        self.root.attributes("-alpha", 0.85)
        self.update_lock_buttons()

    # --------------------------------------------------------
    # DRAGGING
    # --------------------------------------------------------

    def start_drag(self, event):
        if self.locked:
            return
        self.drag_x = event.x_root - self.root.winfo_x()
        self.drag_y = event.y_root - self.root.winfo_y()

    def drag_window(self, event):
        if self.locked:
            return
        x = event.x_root - self.drag_x
        y = event.y_root - self.drag_y
        self.root.geometry(f"+{x}+{y}")

    # --------------------------------------------------------
    # TORN API
    # --------------------------------------------------------

    def fetch_chain_data(self):
        api_key = self.config.get("api_key", "").strip()
        if not api_key:
            raise ValueError("No API key. Click API Key to add it.")

        if self.validated_api_key != api_key:
            faction = self.validate_api_key(api_key)
            self.validated_api_key = api_key
            self.result_queue.put((
                "status",
                f"Verified faction: {faction['name']} (ID {faction['id']})."
            ))

        params = urllib.parse.urlencode({
            "selections": "chain",
            "key": api_key,
            "timestamp": str(int(time.time()))
        })
        request = urllib.request.Request(
            f"{API_URL}?{params}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache"
            }
        )

        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8"))

        if not isinstance(data, dict):
            raise ValueError("Unexpected API response.")

        if "error" in data:
            error = data["error"]
            if isinstance(error, dict):
                raise ValueError(
                    f"API error {error.get('code', '?')}: "
                    f"{error.get('error', 'Unknown error')}"
                )
            raise ValueError(str(error))

        chain = data.get("chain")
        if not isinstance(chain, dict):
            raise ValueError("Response is missing valid chain data.")
        if "timeout" not in chain:
            raise ValueError("Response is missing chain.timeout.")

        raw_timeout = chain["timeout"]
        if isinstance(raw_timeout, bool):
            raise ValueError("Invalid timeout value.")
        try:
            timeout_value = float(raw_timeout)
        except (TypeError, ValueError):
            raise ValueError("Timeout value is not numeric.")
        if not math.isfinite(timeout_value) or timeout_value < 0:
            raise ValueError("Timeout value is invalid or negative.")

        end_value = None
        if chain.get("end") is not None:
            try:
                candidate = float(chain["end"])
                if math.isfinite(candidate) and candidate >= 1_000_000_000:
                    end_value = candidate
            except (TypeError, ValueError):
                pass

        return {"timeout": timeout_value, "end": end_value}

    def refresh_api(self):
        if self.key_validation_in_progress:
            self.set_message("Please wait for API key verification to finish.")
            return
        threading.Thread(target=self.api_request_worker, daemon=True).start()

    def api_request_worker(self):
        # If a request is already active, don't start a duplicate request.
        if not self.request_lock.acquire(blocking=False):
            return
        try:
            result = self.fetch_chain_data()
            self.result_queue.put(("success", result))
        except urllib.error.HTTPError as exc:
            self.result_queue.put(("error", f"HTTP error {exc.code}: {exc.reason}"))
        except urllib.error.URLError as exc:
            self.result_queue.put(("error", f"Network error: {exc.reason}"))
        except Exception as exc:
            self.result_queue.put(("error", str(exc)))
        finally:
            self.request_lock.release()

    def start_polling(self):
        if self.polling:
            self.set_message("Automatic polling is already running.")
            return
        if self.key_validation_in_progress:
            self.set_message("Please wait for API key verification to finish.")
            return
        if not self.config.get("api_key", "").strip():
            self.open_settings()
            self.set_message("Enter and verify your API key to start automatic polling.")
            return

        self.polling = True
        self.poll_stop_event.clear()
        threading.Thread(target=self.polling_worker, daemon=True).start()
        self.set_message("Automatic API polling started (checking every 5 seconds).")

    def stop_polling(self):
        self.polling = False
        self.poll_stop_event.set()
        self.stop_alarm()
        self.set_message("Polling stopped. Countdown retained.")

    def polling_worker(self):
        while not self.poll_stop_event.is_set():
            self.api_request_worker()
            self.poll_stop_event.wait(POLL_INTERVAL)

    # --------------------------------------------------------
    # PROCESS API RESULTS
    # --------------------------------------------------------

    def process_queue(self):
        try:
            while True:
                kind, value = self.result_queue.get_nowait()
                if kind == "success":
                    self.apply_api_timeout(value)
                elif kind == "error":
                    if self.polling:
                        self.set_message(
                            f"API request failed: {value}. Retrying automatically."
                        )
                    else:
                        self.set_message(f"API request failed: {value}")
                elif kind == "status":
                    self.set_message(value)
                elif kind == "key_validated":
                    self.handle_key_validated(value)
                elif kind == "key_validation_error":
                    self.handle_key_validation_error(value)
        except queue.Empty:
            pass

        try:
            if self.root.winfo_exists():
                self.root.after(100, self.process_queue)
        except tk.TclError:
            pass

    def apply_api_timeout(self, result):
        now_mono = time.monotonic()
        timeout_value = result["timeout"]
        end_value = result["end"]

        # Any successful API response proves the connection is alive.
        self.last_success_monotonic = now_mono

        if (
            self.last_timeout_value is None
            or timeout_value != self.last_timeout_value
        ):
            self.last_timeout_value = timeout_value
            self.last_timeout_change_monotonic = now_mono

        if timeout_value == 0 and end_value is None:
            self.deadline = 0
            self.stop_alarm()
            self.play_failure_sound_once()
            self.set_message("API reports an inactive or expired chain.")
            return

        if end_value is not None:
            proposed_deadline = end_value
        else:
            proposed_deadline = time.time() + timeout_value

        # If Torn supplies an end timestamp, use it as the authoritative
        # deadline. If it doesn't, don't reset the countdown just because
        # the API repeats the same timeout value; that would make the
        # countdown jump back up every five seconds.
        if end_value is not None:
            if self.deadline is not None and abs(end_value - self.deadline) < 1:
                self._last_applied_timeout = timeout_value
                self.set_message("API connected. Countdown synchronized.")
                return
            self.deadline = proposed_deadline
            self._last_applied_timeout = timeout_value
        elif self._last_applied_timeout is None or timeout_value != self._last_applied_timeout:
            self.deadline = proposed_deadline
            self._last_applied_timeout = timeout_value
        else:
            # Connection is fresh, but the API repeated the same timeout.
            # Keep the existing local countdown moving instead of resetting it.
            self.set_message("API connected. Timeout value unchanged; retrying automatically.")
            return

        self.failure_sound_played = False
        if self.deadline <= time.time():
            self.stop_alarm()
            self.play_failure_sound_once()
            self.set_message("The chain timer has expired.")
        else:
            self.set_message("API connected. Countdown synchronized.")

    # --------------------------------------------------------
    # COUNTDOWN AND WARNING DISPLAY
    # --------------------------------------------------------

    def set_message(self, message):
        self.last_api_message = message
        try:
            self.status_label.config(text=message)
        except (tk.TclError, AttributeError):
            pass

    def update_warning_labels(self, now):
        if self.last_success_monotonic is None:
            stale_text = "API connection: NOT VERIFIED"
            stale_color = "#e9b44c"
        else:
            age = now - self.last_success_monotonic
            if age >= STALE_AFTER_SECONDS:
                stale_text = f"WARNING: API CONNECTION STALE ({int(age)}s)"
                stale_color = "#ff6262"
            else:
                stale_text = "API connection: OK"
                stale_color = "#63e68b"

        if self.last_timeout_change_monotonic is None:
            unchanged_text = "Timeout: waiting for first valid value"
            unchanged_color = "#e9b44c"
        else:
            age = now - self.last_timeout_change_monotonic
            if age >= UNCHANGED_AFTER_SECONDS:
                unchanged_text = f"WARNING: TIMEOUT UNCHANGED ({int(age)}s)"
                unchanged_color = "#e9b44c"
            else:
                unchanged_text = f"Timeout: last changed {int(age)}s ago"
                unchanged_color = "#63e68b"

        self.normal_stale_label.config(text=stale_text, fg=stale_color)
        self.compact_stale_label.config(text=stale_text, fg=stale_color)
        self.normal_unchanged_label.config(text=unchanged_text, fg=unchanged_color)
        self.compact_unchanged_label.config(text=unchanged_text, fg=unchanged_color)

    def update_display(self):
        now_mono = time.monotonic()
        now_wall = time.time()

        remaining = None
        if self.deadline is not None:
            remaining = max(0, int(math.ceil(self.deadline - now_wall)))

        if remaining is None:
            timer_text = "--:--"
        else:
            timer_text = f"{remaining // 60:02d}:{remaining % 60:02d}"

        color = "#FF3333"
        if remaining is not None and remaining <= 60:
            if now_mono - self.last_flash_toggle >= 0.5:
                self.flash_visible = not self.flash_visible
                self.last_flash_toggle = now_mono
            color = "#ff4d4d" if self.flash_visible else "#17191f"

        self.timer_label.config(text=timer_text, fg=color)
        self.compact_timer_label.config(text=timer_text, fg=color)
        self.update_warning_labels(now_mono)

        if remaining is not None and 0 < remaining <= ALARM_START_SECONDS:
            self.start_alarm()
        if remaining is not None and remaining <= 0:
            self.stop_alarm()
            self.play_failure_sound_once()

        self.root.after(200, self.update_display)

    # --------------------------------------------------------
    # ALARM
    # --------------------------------------------------------

    def start_alarm(self):
        with self.alarm_lock:
            if self.alarm_thread and self.alarm_thread.is_alive():
                return
            self.alarm_stop_event.clear()
            self.alarm_thread = threading.Thread(target=self.alarm_worker, daemon=True)
            self.alarm_thread.start()

    def stop_alarm(self):
        self.alarm_stop_event.set()

    def alarm_worker(self):
        while not self.alarm_stop_event.is_set():
            if self.deadline is None:
                break
            remaining = self.deadline - time.time()
            if remaining <= 0:
                break

            if remaining <= 15:
                frequency = FINAL_BEEP_FREQUENCY
                duration = FINAL_BEEP_DURATION_MS
                pause = FINAL_BEEP_PAUSE_MS
            else:
                frequency = NORMAL_BEEP_FREQUENCY
                duration = NORMAL_BEEP_DURATION_MS
                pause = NORMAL_BEEP_PAUSE_MS

            if winsound is not None:
                try:
                    winsound.Beep(frequency, duration)
                except Exception:
                    pass

            if self.alarm_stop_event.wait(pause / 1000.0):
                break

    def play_failure_sound_once(self):
        if self.failure_sound_played:
            return
        self.failure_sound_played = True
        if winsound is None:
            return

        def play():
            try:
                winsound.Beep(FAILURE_BEEP_FREQUENCY, FAILURE_BEEP_DURATION_MS)
            except Exception:
                pass

        threading.Thread(target=play, daemon=True).start()

    # --------------------------------------------------------
    # CLOSE
    # --------------------------------------------------------

    def close_app(self):
        self.polling = False
        self.poll_stop_event.set()
        self.stop_alarm()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = ChainTimerApp(root)
    root.mainloop()
