import json
import math
import os
import queue
import subprocess
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime, timezone
import tkinter as tk
import webbrowser
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

APP_NAME = "Black Statues Chain Timer"
FACTION_ID = 9412

API_URL = f"https://api.torn.com/faction/{FACTION_ID}"  # Legacy fallback/reference
API_V2_FACTION_CHAIN_URL = "https://api.torn.com/v2/faction/chain"
API_V2_FACTION_ATTACKS_URL = "https://api.torn.com/v2/faction/attacks"
VERIFY_API_URL = "https://api.torn.com/v2/user/faction"

POLL_INTERVAL = 5
CHAIN_TIMEOUT_SECONDS = 300  # Torn resets an active chain to 5 minutes after each successful hit.
CHAIN_HIT_WARNING_MILESTONES = (100, 250, 500, 1_000, 2_500, 5_000, 10_000, 25_000, 50_000, 100_000)
CHAIN_HIT_WARNING_LEAD = 20  # Show a warning during the final 20 hits before each milestone.
STARTUP_SYNC_SECONDS = 600  # Show 10:00 while the app connects and synchronizes with Torn.
PLAYERS_POLL_INTERVAL = 300

# Online presence: heartbeat every 30 seconds; Apps Script considers a timer online for 90 seconds.
ONLINE_HEARTBEAT_INTERVAL = 30
ONLINE_REFRESH_INTERVAL_MS = 15_000

# Google Apps Script connection.
PLAYERS_WEB_APP_URL = "----REDACTED----"
PLAYERS_API_TOKEN = "----REDACTED----"

# Rotate the exposed webhook URLs and put the new URLs here locally.
DISCORD_WEBHOOK_URL = "----REDACTED----"
ONE_MINUTE_FAILSAFE_WEBHOOK_URL = "----REDACTED----"
#ID of role to PING
ONE_MINUTE_FAILSAFE_ROLE_ID = "----REDACTED----"

REQUEST_TIMEOUT = 10
STALE_AFTER_SECONDS = 20
UNCHANGED_AFTER_SECONDS = 60

NORMAL_WIDTH = 390
NORMAL_HEIGHT = 280
COMPACT_WIDTH = 180
COMPACT_HEIGHT = 110
SCREEN_MARGIN = 10

ALARM_START_SECONDS = 60
TEST_MODE = False

SLOW_BEEP_FREQUENCY = 1000
SLOW_BEEP_DURATION_MS = 180
SLOW_BEEP_PAUSE_MS = 350

NORMAL_BEEP_FREQUENCY = 1200
NORMAL_BEEP_DURATION_MS = 120
NORMAL_BEEP_PAUSE_MS = 160

FINAL_BEEP_FREQUENCY = 1800
FINAL_BEEP_DURATION_MS = 100
FINAL_BEEP_PAUSE_MS = 40

FAILURE_BEEP_FREQUENCY = 700
FAILURE_BEEP_DURATION_MS = 8000

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
        self.player_names = []
        self.player_entries = []
        self.player_name_widgets = []
        self.players_message = "Connecting to guard list..."
        self.players_poll_stop_event = threading.Event()

        # Online presence state: each running timer instance has its own ID.
        self.online_client_id = uuid.uuid4().hex
        self.online_presence_stop_event = threading.Event()
        self.online_presence_thread = None
        self.online_identity = None
        self.online_window = None
        self.online_list_frame = None
        self.online_count_label = None
        self.online_status_label = None
        self.online_refresh_after_id = None
        self.online_refresh_in_progress = False

        # Shared live chat state (stored in columns E:H of the existing Timer Online tab).
        self.chat_window = None
        self.chat_text = None
        self.chat_entry = None
        self.chat_status_label = None
        self.chat_refresh_after_id = None
        self.chat_request_in_progress = False
        self.chat_last_message_id = 0

        # Start with a 10:00 synchronization countdown so the UI is useful
        # immediately while the first Torn API responses arrive. The first
        # usable positive API timeout or confirmed hit replaces this grace timer.
        self.deadline_mono = time.monotonic() + STARTUP_SYNC_SECONDS
        self.deadline = time.time() + STARTUP_SYNC_SECONDS  # Wall-clock equivalent.
        self.startup_sync_pending = True
        self.last_timeout_value = None
        self._last_applied_timeout = None
        self.last_chain_current = None
        self.last_chain_start = None
        self.last_success_attack_timestamp = None
        self.last_success_attack_chain = None
        self.last_success_monotonic = None
        self.last_timeout_change_monotonic = None
        self.last_api_message = "Waiting for API connection..."
        self.last_api_timeout_received = None
        self.last_api_end_received = None

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
        self.expiry_handled = False
        self.one_minute_failsafe_sent = False
        # Until Torn confirms the chain state, the startup countdown is only a
        # synchronization grace period and must never trigger a false expiry.
        self.chain_state_unconfirmed = True

        self.speech_deadline = None
        self.spoken_milestones = set()
        self.last_speech_remaining = None

        self.compact_mode = False
        self.locked = False
        self.flash_visible = True
        self.last_flash_toggle = time.monotonic()
        self.drag_x = 0
        self.drag_y = 0

        self.build_interface()
        self.root.protocol("WM_DELETE_WINDOW", self.close_app)
        self.position_top_right(NORMAL_WIDTH, NORMAL_HEIGHT)

        self.set_message("Startup synchronization countdown: 10:00 while connecting to Torn.")
        self.update_display()
        self.process_queue()
        self.root.after(700, self.start_players_polling)
        self.root.after(1200, self.start_online_presence)

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
                "API Key Error", f"Could not save API key:\n{exc}", parent=self.root
            )
            return False

    def call_for_help(self):
        webhook_url = DISCORD_WEBHOOK_URL.strip()
        if not webhook_url.startswith(("https://discord.com/api/webhooks/",
                                       "https://discordapp.com/api/webhooks/")):
            messagebox.showerror(
                "Discord Webhook Not Configured",
                "Set DISCORD_WEBHOOK_URL in the Python file to your rotated webhook URL.",
                parent=self.root
            )
            return
        if not messagebox.askyesno(
            "Call for Help", "Send a CALL FOR HELP alert to Discord now?", parent=self.root
        ):
            return
        threading.Thread(target=self.call_for_help_worker, args=(webhook_url,), daemon=True).start()
        self.set_message("Sending Discord help alert...")

    def call_for_help_worker(self, webhook_url):
        role_id = "626217573406474296"
        payload = {
            "content": f"<@&{role_id}> Help needed!",
            "allowed_mentions": {"parse": [], "roles": [role_id]}
        }
        try:
            request = urllib.request.Request(
                webhook_url, data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json", "User-Agent": "BlackStatuesChainTimer/1.0"},
                method="POST"
            )
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
                if response.status not in (200, 204):
                    raise ValueError(f"Discord returned HTTP {response.status}.")
            self.root.after(0, lambda: self.set_message("Discord help alert sent."))
        except Exception as exc:
            error_text = str(exc)
            self.root.after(0, lambda: self.set_message("Discord help alert failed."))
            self.root.after(0, lambda: messagebox.showerror(
                "Discord Help Alert Failed",
                f"Could not send the alert. Check the webhook URL and connection.\n\n{error_text}",
                parent=self.root
            ))

    def send_one_minute_failsafe(self):
        webhook_url = ONE_MINUTE_FAILSAFE_WEBHOOK_URL.strip()
        if not webhook_url.startswith(("https://discord.com/api/webhooks/",
                                       "https://discordapp.com/api/webhooks/")):
            self.set_message("1-minute failsafe not sent: second Discord webhook is not configured.")
            return
        role_id = ONE_MINUTE_FAILSAFE_ROLE_ID
        payload = {
            "content": f"<@&{role_id}> ⚠️ CHAIN TIMER FAILSAFE: 1 minute remaining!",
            "allowed_mentions": {"parse": [], "roles": [role_id]}
        }
        threading.Thread(
            target=self.one_minute_failsafe_worker, args=(webhook_url, payload), daemon=True
        ).start()

    def one_minute_failsafe_worker(self, webhook_url, payload):
        try:
            request = urllib.request.Request(
                webhook_url, data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json", "User-Agent": "BlackStatuesChainTimer/1.0"},
                method="POST"
            )
            with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
                if response.status not in (200, 204):
                    raise ValueError(f"Discord returned HTTP {response.status}.")
            self.root.after(0, lambda: self.set_message("1-minute failsafe alert sent to Discord."))
        except Exception:
            self.root.after(0, lambda: self.set_message("1-minute failsafe alert failed; check the second webhook."))

    def open_settings(self):
        if self.key_validation_in_progress:
            messagebox.showinfo("API Key", "An API key is already being verified. Please wait.", parent=self.root)
            return
        new_key = simpledialog.askstring(
            "API Key", "Enter your Torn API key:\nOnly keys belonging to faction 9412 are accepted.",
            initialvalue=self.config.get("api_key", ""), show="*", parent=self.root
        )
        if new_key is None:
            return
        new_key = new_key.strip()
        if not new_key:
            messagebox.showwarning("API Key", "The API key cannot be empty.", parent=self.root)
            return
        self.set_message("Verifying API key and faction membership...")
        self.key_validation_in_progress = True
        threading.Thread(target=self.validate_key_worker, args=(new_key,), daemon=True).start()

    # --------------------------------------------------------
    # TORN API KEY VALIDATION
    # --------------------------------------------------------

    def validate_api_key(self, api_key):
        params = urllib.parse.urlencode({"key": api_key, "timestamp": str(int(time.time()))})
        request = urllib.request.Request(
            f"{VERIFY_API_URL}?{params}",
            headers={"User-Agent": "BlackStatuesChainTimer/1.0",
                     "Cache-Control": "no-cache", "Pragma": "no-cache"}
        )
        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8"))
        if not isinstance(data, dict):
            raise ValueError("Torn returned an unexpected verification response.")
        if "error" in data:
            error = data["error"]
            if isinstance(error, dict):
                raise ValueError(f"Torn API error {error.get('code', '?')}: {error.get('error', 'Unknown error')}")
            raise ValueError(str(error))
        faction = data.get("faction")
        if not isinstance(faction, dict):
            raise ValueError(
                "Torn did not return faction information for this API key. Make sure the key has access "
                "to user → faction information and that its owner is currently in a faction."
            )
        try:
            faction_id = int(faction.get("id"))
        except (TypeError, ValueError):
            raise ValueError("Torn returned an invalid faction ID.")
        if faction_id != FACTION_ID:
            faction_name = faction.get("name", "Unknown faction")
            raise ValueError(
                f"This API key belongs to faction '{faction_name}' (ID {faction_id}), "
                f"not BLACK STATUES (ID {FACTION_ID}). The key was not saved."
            )
        return {"id": faction_id, "name": faction.get("name", "BLACK STATUES")}

    def validate_key_worker(self, api_key):
        try:
            faction = self.validate_api_key(api_key)
            self.result_queue.put(("key_validated", {"api_key": api_key, "faction": faction}))
        except urllib.error.HTTPError as exc:
            self.result_queue.put(("key_validation_error", f"HTTP error {exc.code}: {exc.reason}"))
        except urllib.error.URLError as exc:
            self.result_queue.put(("key_validation_error", f"Network error: {exc.reason}"))
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
        self.set_message(f"Verified: {faction['name']} (ID {faction['id']}).")
        if not self.polling:
            self.start_polling()
        else:
            self.refresh_api()

    def handle_key_validation_error(self, error):
        self.key_validation_in_progress = False
        self.set_message("API key verification failed.")
        messagebox.showerror(
            "API Key Rejected",
            f"The API key could not be verified for BLACK STATUES.\n\n{error}\n\nThe new key was not saved.",
            parent=self.root
        )

    # --------------------------------------------------------
    # WINDOW POSITIONING AND LOCK
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

    def toggle_transparency(self):
        current_alpha = float(self.root.attributes("-alpha"))
        current_percent = max(60, min(100, round(current_alpha * 100)))
        selected_percent = simpledialog.askinteger(
            "Window Transparency", "Choose window opacity (60–100):",
            initialvalue=current_percent, minvalue=60, maxvalue=100, parent=self.root
        )
        if selected_percent is None:
            return
        self.root.attributes("-alpha", selected_percent / 100)
        self.transparency_button.config(text=f"{selected_percent}%")

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
        normal_top_controls = tk.Frame(normal_top, bg=bg)
        normal_top_controls.pack(side="right", anchor="ne")
        self.normal_lock_button = tk.Button(
            normal_top_controls, text="🔓", command=self.toggle_lock, font=("Segoe UI Emoji", 9),
            fg="white", bg="#353944", activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=3, padx=0, pady=0, cursor="hand2"
        )
        self.normal_lock_button.pack(side="top", anchor="e")
        self.transparency_button = tk.Button(
            normal_top_controls, text="85%", command=self.toggle_transparency, font=("Segoe UI", 7, "bold"),
            fg="white", bg="#353944", activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=4, padx=0, pady=1, cursor="hand2"
        )
        self.transparency_button.pack(side="top", anchor="e", pady=(2, 0))
        # Normal window only: center the chain timer and hit count in two columns.
        # The compact window deliberately keeps its original single countdown.
        self.countdowns_row = tk.Frame(self.normal_frame, bg=bg)
        self.countdowns_row.pack(fill="x", pady=(3, 2))
        self.countdowns_row.grid_columnconfigure(0, weight=1, uniform="countdown")
        self.countdowns_row.grid_columnconfigure(1, weight=1, uniform="countdown")

        self.timer_column = tk.Frame(self.countdowns_row, bg=bg)
        self.timer_column.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        self.timer_heading = tk.Label(
            self.timer_column, text="TIME LEFT", font=("Segoe UI", 8, "bold"),
            fg="#c5c8d0", bg=bg, anchor="center"
        )
        self.timer_heading.pack(fill="x")
        self.timer_label = tk.Label(
            self.timer_column, text="--:--", font=("Consolas", 29, "bold"),
            fg="#63e68b", bg=bg, anchor="center"
        )
        self.timer_label.pack(fill="x")

        self.chain_count_column = tk.Frame(self.countdowns_row, bg=bg)
        self.chain_count_column.grid(row=0, column=1, sticky="nsew", padx=(4, 0))
        self.chain_count_heading = tk.Label(
            self.chain_count_column, text="CHAIN HITS", font=("Segoe UI", 8, "bold"),
            fg="#c5c8d0", bg=bg, anchor="center"
        )
        self.chain_count_heading.pack(fill="x")
        self.chain_hits_label = tk.Label(
            self.chain_count_column, text="—", font=("Consolas", 24, "bold"),
            fg="#8fc7ff", bg=bg, anchor="center"
        )
        self.chain_hits_label.pack(fill="x")

        # Milestone warning centered below BOTH the timer and chain-hit count.
        # It is packed only while the current count is within 20 hits of a milestone.
        self.chain_milestone_warning_label = tk.Label(
            self.normal_frame, text="", font=("Segoe UI", 9, "bold"),
            fg="#ff6b6b", bg=bg, anchor="center", justify="center"
        )
        self.chain_milestone_warning_visible = False

        # Keep API logs hidden at startup; users can reveal them with the toggle button.
        self.logs_visible = False
        self.diagnostics_frame = tk.Frame(self.normal_frame, bg=bg)
        self.status_label = tk.Label(
            self.diagnostics_frame, text="Waiting for API connection...", font=("Segoe UI", 8),
            fg="#c5c8d0", bg=bg, wraplength=350, justify="center", anchor="center"
        )
        self.status_label.pack(fill="x", pady=(0, 3))
        self.chain_api_debug_label = tk.Label(
            self.diagnostics_frame,
            text="Chain API diagnostics: waiting for first response",
            font=("Consolas", 8), fg="#aeb8c8", bg=bg,
            wraplength=350, justify="center", anchor="center"
        )
        self.chain_api_debug_label.pack(fill="x", pady=(0, 3))
        self.normal_stale_label = tk.Label(
            self.diagnostics_frame, text="WARNING: API connection not verified", font=("Segoe UI", 9, "bold"),
            fg="#e9b44c", bg=bg, anchor="center", justify="center"
        )
        self.normal_stale_label.pack(fill="x")
        self.normal_unchanged_label = tk.Label(
            self.diagnostics_frame, text="Timeout: waiting for first valid value", font=("Segoe UI", 9, "bold"),
            fg="#e9b44c", bg=bg, anchor="center", justify="center"
        )
        self.normal_unchanged_label.pack(fill="x", pady=(1, 3))
        self.players_row = tk.Frame(self.normal_frame, bg=bg)
        self.players_row.pack(fill="x", pady=(3, 5))
        self.players_content = tk.Frame(self.players_row, bg=bg)
        self.players_content.pack(anchor="center")
        self.players_heading = tk.Label(
            self.players_content, text="Guards :", font=("Segoe UI", 9, "bold"),
            fg="#8fc7ff", bg=bg, anchor="e", justify="right"
        )
        self.players_heading.grid(row=0, column=0, padx=(0, 8), sticky="e")
        self.players_list_frame = tk.Frame(self.players_content, bg=bg)
        self.players_list_frame.grid(row=0, column=1, sticky="w")
        self.players_label = tk.Label(
            self.players_list_frame, text=self.players_message, font=("Segoe UI", 9),
            fg="white", bg=bg, anchor="w", justify="left", wraplength=225
        )
        self.players_label.pack(anchor="w")
        self.players_content.grid_columnconfigure(0, weight=0)
        self.players_content.grid_columnconfigure(1, weight=0)
        self.players_content.grid_rowconfigure(0, weight=0)
        button_frame = tk.Frame(self.normal_frame, bg=bg)
        button_frame.pack(fill="x", pady=(1, 0))
        for text, command in [
            ("API Key", self.open_settings),
            ("Small Countdown", self.toggle_countdown_mode),
            ("Start", self.start_polling),
            ("Stop", self.stop_polling),
            ("Refresh", self.refresh_api),
            ("Online", self.open_online_window),
        ]:
            tk.Button(
                button_frame, text=text, command=command, font=("Segoe UI", 8),
                fg="white", bg="#353944", activebackground="#505666", activeforeground="white",
                relief="flat", bd=0, padx=3, pady=4, cursor="hand2"
            ).pack(side="left", expand=True, fill="x", padx=2)
        self.logs_toggle_button = tk.Button(
            self.normal_frame, text="Show API Logs", width=12, command=self.toggle_logs,
            font=("Segoe UI", 8, "bold"), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white", relief="flat", bd=0,
            padx=0, pady=3, cursor="hand2"
        )
        self.logs_toggle_button.pack(anchor="center", pady=(3, 0))
        self.normal_help_button = tk.Button(
            self.normal_frame, text="CALL FOR HELP", command=self.call_for_help,
            font=("Segoe UI", 10, "bold"), fg="white", bg="#a83232",
            activebackground="#c74444", activeforeground="white", relief="flat", bd=0,
            padx=8, pady=8, height=2, cursor="hand2"
        )
        self.normal_help_button.pack(side="bottom", fill="x", expand=False, pady=(2, 0))
        self.compact_frame = tk.Frame(self.root, bg=bg, padx=6, pady=3)
        compact_top = tk.Frame(self.compact_frame, bg=bg)
        compact_top.pack(fill="x")
        self.expand_button = tk.Button(
            compact_top, text="↗", command=self.toggle_countdown_mode, font=("Segoe UI", 10, "bold"),
            fg="white", bg="#353944", activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=2, padx=0, pady=0, cursor="hand2"
        )
        self.expand_button.pack(side="left")
        self.compact_lock_button = tk.Button(
            compact_top, text="🔓", command=self.toggle_lock, font=("Segoe UI Emoji", 8),
            fg="white", bg="#353944", activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=3, padx=0, pady=0, cursor="hand2"
        )
        self.compact_lock_button.pack(side="right")
        self.compact_title = tk.Label(
            compact_top, text=APP_NAME, font=("Segoe UI", 8, "bold"),
            fg="white", bg=bg, anchor="center"
        )
        self.compact_title.pack(side="left", fill="x", expand=True)
        self.compact_timer_label = tk.Label(
            self.compact_frame, text="--:--", font=("Consolas", 21, "bold"),
            fg="#63e68b", bg=bg, anchor="center"
        )
        self.compact_timer_label.pack(fill="x")
        self.compact_stale_label = tk.Label(
            self.compact_frame, text="WARNING: API connection not verified",
            font=("Segoe UI", 7, "bold"), fg="#e9b44c", bg=bg, anchor="center", justify="center"
        )
        self.compact_stale_label.pack(fill="x")
        self.compact_unchanged_label = tk.Label(
            self.compact_frame, text="Timeout: waiting for first valid value",
            font=("Segoe UI", 7, "bold"), fg="#e9b44c", bg=bg, anchor="center", justify="center"
        )
        self.compact_unchanged_label.pack(fill="x")
        drag_widgets = [
            self.root, self.normal_frame, normal_top, self.title_label, self.countdowns_row,
            self.timer_column, self.timer_heading, self.timer_label,
            self.chain_count_column, self.chain_count_heading, self.chain_hits_label,
            self.chain_milestone_warning_label, self.diagnostics_frame, self.status_label, self.normal_stale_label, self.normal_unchanged_label,
            self.players_row, self.players_content, self.players_heading, self.players_label,
            self.logs_toggle_button,
            self.compact_frame, compact_top, self.compact_title, self.compact_timer_label,
            self.compact_stale_label, self.compact_unchanged_label
        ]
        for widget in drag_widgets:
            widget.bind("<ButtonPress-1>", self.start_drag)
            widget.bind("<B1-Motion>", self.drag_window)
        self.update_lock_buttons()

    # --------------------------------------------------------
    # MODE SWITCHING AND DRAGGING
    # --------------------------------------------------------

    def toggle_logs(self):
        """Show or hide API status messages and diagnostic warnings in normal mode."""
        if self.compact_mode:
            return
        if self.logs_visible:
            self.diagnostics_frame.pack_forget()
            self.logs_visible = False
            self.logs_toggle_button.config(text="Show API Logs")
        else:
            # Reinsert diagnostics after the countdown and before the players row.
            self.diagnostics_frame.pack(fill="x", pady=(0, 3), before=self.players_row)
            self.logs_visible = True
            self.logs_toggle_button.config(text="Hide API Logs")
        self.root.update_idletasks()
        required_height = self.normal_frame.winfo_reqheight()
        normal_height = max(235, required_height + 10)
        self.position_top_right(NORMAL_WIDTH, normal_height)
        self.root.attributes("-topmost", True)

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
            self.root.update_idletasks()
            required_height = self.normal_frame.winfo_reqheight()
            normal_height = max(NORMAL_HEIGHT, required_height) + 10
            self.position_top_right(NORMAL_WIDTH, normal_height)
            self.root.attributes("-topmost", True)
            current_percent = round(float(self.root.attributes("-alpha")) * 100)
            self.transparency_button.config(text=f"{current_percent}%")
            self.update_lock_buttons()

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
    # GOOGLE SHEETS PLAYER NAMES
    # --------------------------------------------------------

    def open_torn_profile(self, player_id):
        if str(player_id).isdigit() and int(player_id) > 0:
            webbrowser.open(f"https://www.torn.com/profiles.php?XID={int(player_id)}")

    def update_players_label(self):
        try:
            for widget in self.player_name_widgets:
                widget.destroy()
            self.player_name_widgets = []
            if self.player_entries:
                self.players_label.pack_forget()
                for player in self.player_entries:
                    name = player.get("name", "").strip()
                    player_id = str(player.get("id", "")).strip()
                    if not name:
                        continue
                    if player_id.isdigit() and int(player_id) > 0:
                        widget = tk.Label(
                            self.players_list_frame, text=name, font=("Segoe UI", 9, "underline"),
                            fg="#75baff", bg=self.players_content.cget("bg"), cursor="hand2",
                            anchor="w", justify="left", wraplength=225
                        )
                        widget.bind("<Button-1>", lambda event, pid=player_id: self.open_torn_profile(pid))
                    else:
                        widget = tk.Label(
                            self.players_list_frame, text=name, font=("Segoe UI", 9),
                            fg="white", bg=self.players_content.cget("bg"),
                            anchor="w", justify="left", wraplength=225
                        )
                    widget.pack(anchor="w")
                    self.player_name_widgets.append(widget)
            else:
                self.players_label.config(text=self.players_message)
                self.players_label.pack(anchor="w")
            self.root.update_idletasks()
        except (tk.TclError, AttributeError):
            pass

    def extract_player_entries(self, data):
        entries = []

        def add_entry(value, fallback_id=""):
            if isinstance(value, dict):
                name = str(value.get("name") or value.get("playerName") or value.get("player_name") or "").strip()
                player_id = str(value.get("id") or value.get("playerId") or value.get("player_id") or fallback_id or "").strip()
            elif isinstance(value, str):
                name, player_id = value.strip(), str(fallback_id or "").strip()
            else:
                return
            if name and not any(p["id"] == player_id and p["name"].lower() == name.lower() for p in entries):
                entries.append({"id": player_id, "name": name})

        if isinstance(data, dict):
            for key in ("players", "names", "checkedPlayers", "checked_players", "data"):
                value = data.get(key)
                if isinstance(value, list):
                    for item in value:
                        add_entry(item)
                    if entries:
                        break
        elif isinstance(data, list):
            if data and isinstance(data[0], list):
                ids = data[0] if len(data) > 0 else []
                names = data[1] if len(data) > 1 else []
                for index, name in enumerate(names):
                    add_entry(name, ids[index] if index < len(ids) else "")
            else:
                for item in data:
                    add_entry(item)
        return entries

    def fetch_players(self):
        url = PLAYERS_WEB_APP_URL.strip()
        token = PLAYERS_API_TOKEN.strip()
        if not url or "PASTE_YOUR_DEPLOYED_APPS_SCRIPT_EXEC_URL_HERE" in url or not url.startswith("https://script.google.com/macros/s/"):
            raise ValueError("Set PLAYERS_WEB_APP_URL in the Python file to your deployed Apps Script /exec URL.")
        if not token or token.startswith("REPLACE_WITH_"):
            raise ValueError("Set PLAYERS_API_TOKEN in the Python file to the same token stored in Apps Script Properties.")
        separator = "&" if "?" in url else "?"
        query = urllib.parse.urlencode({"token": token, "_ts": str(int(time.time()))})
        request = urllib.request.Request(
            f"{url}{separator}{query}",
            headers={"User-Agent": "BlackStatuesChainTimer/1.0", "Cache-Control": "no-cache", "Pragma": "no-cache"}
        )
        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8-sig"))
        if isinstance(data, dict):
            message = str(data.get("message") or data.get("error") or "")
            if data.get("ok") is False and "Unauthorized" in message:
                raise ValueError(
                    "The URL is still serving an OLD Apps Script deployment (its response says Unauthorized). "
                    "Update the Web app deployment to the latest code."
                )
            if data.get("ok") is False:
                raise ValueError(message or "Apps Script returned ok=false.")
            if data.get("error"):
                raise ValueError(message)
        players = self.extract_player_entries(data)
        if isinstance(data, dict) and not players and data.get("players") is None:
            raise ValueError("Apps Script response did not contain a 'players' list. Update the On Duty Apps Script endpoint.")
        return players

    def refresh_players(self):
        if (not PLAYERS_WEB_APP_URL.strip()
                or "PASTE_YOUR_DEPLOYED_APPS_SCRIPT_EXEC_URL_HERE" in PLAYERS_WEB_APP_URL
                or not PLAYERS_API_TOKEN.strip() or PLAYERS_API_TOKEN.startswith("REPLACE_WITH_")):
            self.players_message = "Set the Apps Script URL and token in the Python file"
            self.update_players_label()
            return
        threading.Thread(target=self.players_request_worker, daemon=True).start()

    def players_request_worker(self):
        try:
            self.result_queue.put(("players_success", self.fetch_players()))
        except urllib.error.HTTPError as exc:
            self.result_queue.put(("players_error", f"HTTP error {exc.code}: {exc.reason}"))
        except urllib.error.URLError as exc:
            self.result_queue.put(("players_error", f"Network error: {exc.reason}"))
        except Exception as exc:
            self.result_queue.put(("players_error", str(exc)))

    def start_players_polling(self):
        if self.players_poll_stop_event.is_set():
            return
        self.refresh_players()
        self.root.after(PLAYERS_POLL_INTERVAL * 1000, self.start_players_polling)

    def handle_players_success(self, players):
        self.player_entries = players
        self.player_names = [player.get("name", "") for player in players]
        self.players_message = f"{len(players)} checked player(s)" if players else "No players found in On Duty row 2"
        self.update_players_label()

    # --------------------------------------------------------
    # ONLINE PRESENCE
    # --------------------------------------------------------

    def start_online_presence(self):
        """Start a background heartbeat loop for this timer instance."""
        if self.online_presence_thread and self.online_presence_thread.is_alive():
            return
        self.online_presence_stop_event.clear()
        self.online_presence_thread = threading.Thread(
            target=self.online_presence_worker, daemon=True
        )
        self.online_presence_thread.start()

    def fetch_online_identity(self, api_key):
        """Resolve the identity belonging to the API key currently configured in this timer.

        Do not hard-code a player ID or name here: each faction member runs their own
        copy of the timer, and the heartbeat must represent the owner of that API key.
        """
        api_key = str(api_key or "").strip()
        if not api_key:
            raise ValueError("Enter a Torn API key before enabling Online presence.")

        # Torn's v1 user/basic response includes player_id and name for the key owner.
        params = urllib.parse.urlencode({
            "selections": "basic",
            "key": api_key,
            "timestamp": str(int(time.time())),
        })
        request = urllib.request.Request(
            f"https://api.torn.com/user/?{params}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
            },
        )
        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8-sig"))

        if not isinstance(data, dict):
            raise ValueError("Torn returned an unexpected user identity response.")
        if "error" in data:
            error = data["error"]
            if isinstance(error, dict):
                raise ValueError(
                    f"Torn identity lookup error {error.get('code', '?')}: "
                    f"{error.get('error', 'Unknown error')}"
                )
            raise ValueError(str(error))

        player_id = str(data.get("player_id") or data.get("playerid") or data.get("id") or "").strip()
        player_name = str(data.get("name") or "").strip()
        if not player_id.isdigit() or int(player_id) <= 0 or not player_name:
            raise ValueError(
                "Torn did not return the player ID and name for this API key. "
                "Check that the key has access to the user basic selection."
            )
        return {"id": player_id, "name": player_name}

    def presence_request(self, action, extra_params=None, timeout=REQUEST_TIMEOUT):
        """Call the protected Apps Script endpoint for an Online presence action."""
        url = PLAYERS_WEB_APP_URL.strip()
        token = PLAYERS_API_TOKEN.strip()
        if not url.startswith("https://script.google.com/macros/s/") or not token:
            raise ValueError("The Apps Script URL or token is not configured.")
        params = {"token": token, "action": action, "_ts": str(int(time.time()))}
        if extra_params:
            params.update(extra_params)
        separator = "&" if "?" in url else "?"
        request = urllib.request.Request(
            f"{url}{separator}{urllib.parse.urlencode(params)}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
            },
        )
        with urllib.request.urlopen(request, timeout=timeout) as response:
            data = json.loads(response.read().decode("utf-8-sig"))
        if not isinstance(data, dict):
            raise ValueError("Apps Script returned an unexpected Online response.")
        if data.get("ok") is False:
            raise ValueError(str(data.get("error") or "Apps Script Online request failed."))
        return data

    def online_presence_worker(self):
        """Send a heartbeat every 30 seconds; retry identity lookup at a relaxed cadence."""
        current_key = None
        identity = None
        next_identity_retry = 0.0
        next_heartbeat = 0.0
        while not self.online_presence_stop_event.is_set():
            api_key = str(self.config.get("api_key", "") or "").strip()
            now = time.monotonic()

            if not api_key:
                identity = None
                self.online_identity = None
                current_key = None
                self.online_presence_stop_event.wait(5)
                continue

            if api_key != current_key:
                current_key = api_key
                identity = None
                self.online_identity = None
                next_identity_retry = 0.0
                next_heartbeat = 0.0

            if identity is None and now >= next_identity_retry:
                try:
                    identity = self.fetch_online_identity(api_key)
                    self.online_identity = identity
                    next_heartbeat = 0.0
                except Exception as exc:
                    # Show the actual cause in the Online window; retry without affecting countdown.
                    self.result_queue.put(("online_presence_status", f"Identity lookup failed: {exc}"))
                    next_identity_retry = time.monotonic() + 30.0

            if identity and time.monotonic() >= next_heartbeat:
                try:
                    heartbeat_result = self.presence_request(
                        "heartbeat",
                        {
                            "id": identity["id"],
                            "name": identity["name"],
                            "client_id": self.online_client_id,
                        },
                        timeout=REQUEST_TIMEOUT,
                    )
                    # Do not report success just because the endpoint returned valid JSON.
                    # Verify that the deployed Apps Script actually handled the heartbeat.
                    if heartbeat_result.get("action") != "heartbeat":
                        raise ValueError(
                            "Apps Script did not confirm a heartbeat. Response: "
                            + json.dumps(heartbeat_result, ensure_ascii=False)[:500]
                        )
                    server_last_seen = heartbeat_result.get("last_seen")
                    if not server_last_seen:
                        raise ValueError(
                            "Apps Script confirmed no heartbeat timestamp. Response: "
                            + json.dumps(heartbeat_result, ensure_ascii=False)[:500]
                        )
                except Exception as exc:
                    # The next heartbeat retries; the 90-second server-side window
                    # naturally expires a disconnected or unreachable timer.
                    self.result_queue.put(("online_presence_status", f"Heartbeat failed: {exc}"))
                else:
                    self.result_queue.put((
                        "online_presence_status",
                        f"Heartbeat confirmed at {time.strftime('%H:%M:%S')} local time | "
                        f"ID {identity['id']} | client {self.online_client_id[:8]} | "
                        f"server ms {server_last_seen}"
                    ))
                next_heartbeat = time.monotonic() + ONLINE_HEARTBEAT_INTERVAL

            self.online_presence_stop_event.wait(2)

    def open_online_window(self):
        """Open the combined live chat and online-timers window."""
        try:
            if self.online_window is not None and self.online_window.winfo_exists():
                self.online_window.deiconify()
                self.online_window.lift()
                self.refresh_online_players()
                self.refresh_chat()
                return
        except tk.TclError:
            pass

        window = tk.Toplevel(self.root)
        self.online_window = window
        # Chat and online presence now live together in one resizable window.
        self.chat_window = window
        window.title("Black Statues — Live Chat & Online")
        window.geometry("820x540")
        window.minsize(620, 360)
        window.configure(bg="#17191f")
        window.attributes("-topmost", True)
        window.protocol("WM_DELETE_WINDOW", self.close_online_window)

        header = tk.Frame(window, bg="#17191f", padx=14, pady=10)
        header.pack(fill="x")
        title_row = tk.Frame(header, bg="#17191f")
        title_row.pack(fill="x")
        tk.Label(title_row, text="BLACK STATUES", font=("Segoe UI", 14, "bold"),
                 fg="white", bg="#17191f").pack(side="left")
        tk.Label(title_row, text="LIVE FACTION CHAT", font=("Segoe UI", 9, "bold"),
                 fg="#63e68b", bg="#17191f").pack(side="left", padx=(12, 0), pady=(3, 0))
        tk.Label(header, text="Messages sync automatically • newest 50 shown • older messages stay in the sheet",
                 font=("Segoe UI", 8), fg="#aeb8c8", bg="#17191f").pack(anchor="w", pady=(3, 0))

        controls = tk.Frame(window, bg="#17191f", padx=14, pady=0)
        controls.pack(fill="x")
        tk.Button(controls, text="Refresh online list", command=self.refresh_online_players,
                  font=("Segoe UI", 8, "bold"), fg="white", bg="#353944",
                  activebackground="#505666", activeforeground="white", relief="flat", bd=0,
                  padx=10, pady=5, cursor="hand2").pack(side="left")
        tk.Label(controls, text="Online list refreshes every 15 seconds · chat every 5 seconds",
                 font=("Segoe UI", 8), fg="#aeb8c8", bg="#17191f").pack(side="right")

        # Main area expands/shrinks with the window. Chat takes most of the width;
        # online players stay in a narrower panel on the right.
        content = tk.Frame(window, bg="#17191f", padx=12, pady=0)
        content.pack(fill="both", expand=True)
        content.grid_rowconfigure(0, weight=1)
        content.grid_columnconfigure(0, weight=7, minsize=350)
        content.grid_columnconfigure(1, weight=3, minsize=180)

        chat_panel = tk.Frame(content, bg="#20242c", highlightthickness=1,
                              highlightbackground="#343b47")
        chat_panel.grid(row=0, column=0, sticky="nsew", padx=(0, 8))
        online_panel = tk.Frame(content, bg="#1d2128", highlightthickness=1,
                                highlightbackground="#343b47")
        online_panel.grid(row=0, column=1, sticky="nsew")

        chat_heading = tk.Frame(chat_panel, bg="#20242c", padx=10, pady=8)
        chat_heading.pack(fill="x")
        tk.Label(chat_heading, text="Faction chat", font=("Segoe UI", 11, "bold"),
                 fg="white", bg="#20242c").pack(side="left")
        tk.Label(chat_heading, text="● LIVE", font=("Segoe UI", 8, "bold"),
                 fg="#63e68b", bg="#20242c").pack(side="right")

        # Pack the composer at the bottom BEFORE the expanding message area so it
        # remains visible even when the window is short or resized smaller.
        composer = tk.Frame(chat_panel, bg="#20242c", padx=8, pady=8)
        composer.pack(side="bottom", fill="x")
        self.chat_status_label = tk.Label(composer, text="Connecting to shared chat…",
                                          anchor="w", font=("Segoe UI", 8),
                                          fg="#aeb8c8", bg="#20242c")
        self.chat_status_label.pack(fill="x", pady=(0, 5))
        input_row = tk.Frame(composer, bg="#20242c")
        input_row.pack(fill="x")
        self.chat_entry = tk.Entry(input_row, bg="#292f39", fg="white", insertbackground="white",
                                   relief="flat", font=("Segoe UI", 10))
        self.chat_entry.pack(side="left", fill="x", expand=True, ipady=8, padx=(0, 7))
        self.chat_entry.bind("<Return>", lambda _event: self.send_chat_message())
        tk.Button(input_row, text="Send", command=self.send_chat_message,
                  font=("Segoe UI", 9, "bold"), fg="white", bg="#287a4b",
                  activebackground="#32965d", activeforeground="white", relief="flat", bd=0,
                  padx=16, pady=7, cursor="hand2").pack(side="right")

        messages_area = tk.Frame(chat_panel, bg="#20242c", padx=8, pady=0)
        messages_area.pack(side="top", fill="both", expand=True)
        self.chat_text = tk.Text(messages_area, state="disabled", wrap="word", bg="#20242c",
                                 fg="#edf0f5", insertbackground="white", relief="flat",
                                 padx=8, pady=7, font=("Segoe UI", 9), spacing1=2, spacing3=5,
                                 borderwidth=0, highlightthickness=0)
        chat_scroll = tk.Scrollbar(messages_area, orient="vertical", command=self.chat_text.yview)
        self.chat_text.configure(yscrollcommand=chat_scroll.set)
        chat_scroll.pack(side="right", fill="y")
        self.chat_text.pack(side="left", fill="both", expand=True)
        self.chat_text.tag_configure("sender", foreground="#75baff", font=("Segoe UI", 9, "bold"))
        self.chat_text.tag_configure("time", foreground="#929baa", font=("Segoe UI", 8))
        self.chat_text.tag_configure("message", foreground="#edf0f5", font=("Segoe UI", 9))

        online_header = tk.Frame(online_panel, bg="#1d2128", padx=10, pady=9)
        online_header.pack(fill="x")
        tk.Label(online_header, text="ONLINE NOW", font=("Segoe UI", 10, "bold"),
                 fg="white", bg="#1d2128").pack(anchor="w")
        self.online_count_label = tk.Label(online_header, text="Checking online timers…",
                                           font=("Segoe UI", 8, "bold"), fg="#63e68b",
                                           bg="#1d2128", anchor="w")
        self.online_count_label.pack(fill="x", pady=(3, 0))
        self.online_status_label = tk.Label(online_header, text="Checking this timer's connection…",
                                            font=("Segoe UI", 7), fg="#aeb8c8", bg="#1d2128",
                                            anchor="w", justify="left", wraplength=210)
        self.online_status_label.pack(fill="x", pady=(4, 0))
        online_body = tk.Frame(online_panel, bg="#1d2128", padx=8, pady=0)
        online_body.pack(fill="both", expand=True)
        online_canvas = tk.Canvas(online_body, bg="#1d2128", highlightthickness=0, bd=0)
        online_scroll = tk.Scrollbar(online_body, orient="vertical", command=online_canvas.yview)
        self.online_list_frame = tk.Frame(online_canvas, bg="#1d2128")
        self.online_list_frame.bind(
            "<Configure>", lambda _event: online_canvas.configure(scrollregion=online_canvas.bbox("all"))
        )
        online_canvas_window = online_canvas.create_window((0, 0), window=self.online_list_frame,
                                                           anchor="nw")
        online_canvas.bind("<Configure>", lambda event: online_canvas.itemconfigure(
            online_canvas_window, width=event.width
        ))
        online_canvas.configure(yscrollcommand=online_scroll.set)
        online_canvas.pack(side="left", fill="both", expand=True)
        online_scroll.pack(side="right", fill="y")

        self.refresh_online_players()
        self.schedule_online_refresh()
        self.refresh_chat()
        self.schedule_chat_refresh()
        self.chat_entry.focus_set()

    def close_online_window(self):
        """Close the combined chat/online window and cancel both refresh loops."""
        for attr in ("online_refresh_after_id", "chat_refresh_after_id"):
            after_id = getattr(self, attr, None)
            if after_id is not None:
                try:
                    self.root.after_cancel(after_id)
                except tk.TclError:
                    pass
                setattr(self, attr, None)
        if self.online_window is not None:
            try:
                self.online_window.destroy()
            except tk.TclError:
                pass
        self.online_window = None
        self.chat_window = None
        self.online_list_frame = None
        self.online_count_label = None
        self.online_status_label = None
        self.chat_text = None
        self.chat_entry = None
        self.chat_status_label = None
        self.chat_request_in_progress = False

    def schedule_online_refresh(self):
        self.online_refresh_after_id = None
        try:
            if self.online_window is not None and self.online_window.winfo_exists():
                self.online_refresh_after_id = self.root.after(
                    ONLINE_REFRESH_INTERVAL_MS, self._scheduled_online_refresh
                )
        except tk.TclError:
            pass

    def _scheduled_online_refresh(self):
        self.online_refresh_after_id = None
        self.refresh_online_players()
        self.schedule_online_refresh()

    def refresh_online_players(self):
        try:
            if self.online_window is None or not self.online_window.winfo_exists():
                return
        except tk.TclError:
            return
        if self.online_refresh_in_progress:
            return
        self.online_refresh_in_progress = True
        threading.Thread(target=self.online_players_request_worker, daemon=True).start()

    def online_players_request_worker(self):
        try:
            data = self.presence_request("online")
            online = data.get("online", [])
            if not isinstance(online, list):
                raise ValueError("Apps Script returned an invalid online player list.")
            self.result_queue.put(("online_success", online))
        except Exception as exc:
            self.result_queue.put(("online_error", str(exc)))

    def update_online_window(self, online):
        try:
            if self.online_window is None or not self.online_window.winfo_exists():
                return

            # Show each Torn player exactly once, even if multiple timer
            # instances (and therefore multiple client IDs) are sending heartbeats.
            # Keep the most recent heartbeat for that player.
            latest_by_player = {}
            for player in online if isinstance(online, list) else []:
                if not isinstance(player, dict):
                    continue
                player_id = str(player.get("id") or "").strip()
                if not player_id:
                    continue
                try:
                    last_seen = int(player.get("last_seen") or 0)
                except (TypeError, ValueError):
                    last_seen = 0
                current = latest_by_player.get(player_id)
                if current is None or last_seen > current[0]:
                    latest_by_player[player_id] = (last_seen, player)
            online = [item[1] for item in latest_by_player.values()]

            if self.online_count_label is not None:
                self.online_count_label.config(
                    text=f"{len(online)} player(s) online",
                    fg="#63e68b" if online else "#e9b44c",
                )
            if self.online_list_frame is None:
                return
            for widget in self.online_list_frame.winfo_children():
                widget.destroy()
            if not online:
                tk.Label(
                    self.online_list_frame,
                    text="No players have sent a heartbeat in the last 90 seconds.",
                    font=("Segoe UI", 10), fg="#c5c8d0", bg="#17191f",
                    wraplength=270, justify="left", anchor="w"
                ).pack(fill="x", pady=8)
                return
            online = sorted(
                online,
                key=lambda player: str(player.get("name", "")).lower()
            )
            now_ms = int(time.time() * 1000)
            for player in online:
                name = str(player.get("name") or "Unknown player")
                player_id = str(player.get("id") or "")
                last_seen = player.get("last_seen")
                try:
                    age = max(0, int((now_ms - int(last_seen)) / 1000))
                    seen_text = "just now" if age < 5 else f"{age}s ago"
                except (TypeError, ValueError):
                    seen_text = "recently"
                card = tk.Frame(
                    self.online_list_frame, bg="#252a33", padx=10, pady=8,
                    highlightthickness=1, highlightbackground="#3a414d"
                )
                card.pack(fill="x", pady=(0, 7))
                line = tk.Frame(card, bg="#252a33")
                line.pack(fill="x")
                tk.Label(
                    line, text="●", font=("Segoe UI", 12, "bold"),
                    fg="#63e68b", bg="#252a33"
                ).pack(side="left", padx=(0, 7))
                tk.Label(
                    line, text=name, font=("Segoe UI", 10, "bold"),
                    fg="white", bg="#252a33", anchor="w", justify="left",
                    wraplength=220
                ).pack(side="left", fill="x", expand=True)
                tk.Label(
                    card, text=f"Player ID: {player_id}", font=("Consolas", 8),
                    fg="#aeb8c8", bg="#252a33", anchor="w"
                ).pack(fill="x", pady=(4, 0))
                tk.Label(
                    card, text=f"Last heartbeat: {seen_text}", font=("Segoe UI", 8),
                    fg="#63e68b", bg="#252a33", anchor="w"
                ).pack(fill="x", pady=(2, 0))
        except tk.TclError:
            pass

    def update_online_presence_status(self, status):
        try:
            if self.online_window is not None and self.online_window.winfo_exists() and self.online_status_label is not None:
                is_error = "failed:" in str(status).lower()
                self.online_status_label.config(
                    text=str(status), fg="#ff9c9c" if is_error else "#aeb8c8"
                )
        except tk.TclError:
            pass

    def update_online_error(self, error):
        try:
            if self.online_window is None or not self.online_window.winfo_exists():
                return
            if self.online_count_label is not None:
                self.online_count_label.config(text="Could not load online timers", fg="#ff6262")
            if self.online_list_frame is not None:
                for widget in self.online_list_frame.winfo_children():
                    widget.destroy()
                tk.Label(
                    self.online_list_frame, text=str(error), font=("Segoe UI", 9),
                    fg="#ff9c9c", bg="#17191f", wraplength=270, justify="left", anchor="w"
                ).pack(fill="x", pady=8)
        except tk.TclError:
            pass

    def send_offline_presence(self):
        identity = self.online_identity
        if not isinstance(identity, dict):
            return
        try:
            self.presence_request(
                "offline",
                {"id": identity["id"], "client_id": self.online_client_id},
                timeout=4,
            )
        except Exception:
            # If the endpoint is unreachable, the row ages out after 90 seconds.
            pass

    # --------------------------------------------------------
    # SHARED LIVE CHAT
    # --------------------------------------------------------

    def open_chat_window(self):
        """Compatibility alias: chat is now embedded in the Online window."""
        self.open_online_window()

    def close_chat_window(self):
        """Compatibility alias: closing chat closes the combined Online window."""
        self.close_online_window()

    def schedule_chat_refresh(self):
        self.chat_refresh_after_id = None
        try:
            if self.chat_window is not None and self.chat_window.winfo_exists():
                self.chat_refresh_after_id = self.root.after(5000, self._scheduled_chat_refresh)
        except tk.TclError:
            pass

    def _scheduled_chat_refresh(self):
        self.chat_refresh_after_id = None
        self.refresh_chat()
        self.schedule_chat_refresh()

    def refresh_chat(self):
        try:
            if self.chat_window is None or not self.chat_window.winfo_exists():
                return
        except tk.TclError:
            return
        if self.chat_request_in_progress:
            return
        self.chat_request_in_progress = True
        threading.Thread(target=self.chat_request_worker, args=("chat_recent", None), daemon=True).start()

    def chat_request_worker(self, action, extra_params):
        try:
            data = self.presence_request(action, extra_params, timeout=REQUEST_TIMEOUT)
            if action == "chat_send":
                self.result_queue.put(("chat_send_success", data))
            else:
                self.result_queue.put(("chat_success", data.get("messages", [])))
        except Exception as exc:
            self.result_queue.put(("chat_error", str(exc)))

    def send_chat_message(self):
        try:
            if self.chat_entry is None or not self.chat_entry.winfo_exists():
                return
        except tk.TclError:
            return
        message = self.chat_entry.get().strip()
        if not message:
            return
        if len(message) > 500:
            messagebox.showwarning("Message too long", "Chat messages must be 500 characters or fewer.", parent=self.chat_window)
            return
        identity = self.online_identity
        if not isinstance(identity, dict) or not identity.get("id") or not identity.get("name"):
            if self.chat_status_label is not None:
                self.chat_status_label.config(text="Waiting for Torn identity lookup. Check that your API key has user → basic access.", fg="#ffbf69")
            return
        self.chat_entry.delete(0, "end")
        self.chat_entry.config(state="disabled")
        if self.chat_status_label is not None:
            self.chat_status_label.config(text="Sending message…", fg="#aeb8c8")
        params = {"id": str(identity["id"]), "name": str(identity["name"]),
                  "client_id": self.online_client_id, "message": message}
        threading.Thread(target=self.chat_request_worker, args=("chat_send", params), daemon=True).start()

    def update_chat_messages(self, messages):
        """Render shared chat messages using the numeric Unix-ms timestamp when available.

        The numeric timestamp is authoritative. It avoids displaying spreadsheet/date
        serial values such as Sat Dec 30 1899 when the Apps Script's formatted `time`
        field is stale or incorrectly converted. All displayed timestamps use UTC.
        """
        if self.chat_text is None:
            return
        try:
            if not self.chat_text.winfo_exists():
                return
            was_at_bottom = self.chat_text.yview()[1] >= 0.98
            self.chat_text.configure(state="normal")
            self.chat_text.delete("1.0", "end")
            if not messages:
                self.chat_text.insert("end", "No messages yet. Say hello to your faction!\n", "message")
            for item in messages[-50:]:
                sender = str(item.get("name") or "Unknown")
                message = str(item.get("message") or "")

                # Apps Script stores Date.now() in milliseconds. Prefer that raw
                # numeric value over `time`, which may come from an old deployment.
                timestamp = ""
                raw_timestamp = item.get("timestamp")
                try:
                    if raw_timestamp is not None and str(raw_timestamp).strip() != "":
                        numeric_timestamp = float(raw_timestamp)
                        if math.isfinite(numeric_timestamp) and numeric_timestamp > 0:
                            # Also tolerate Unix seconds if an older endpoint sends seconds.
                            if numeric_timestamp < 100_000_000_000:
                                numeric_timestamp *= 1000
                            timestamp = datetime.fromtimestamp(
                                numeric_timestamp / 1000.0, tz=timezone.utc
                            ).strftime("%Y-%m-%d %H:%M:%S UTC")
                except (TypeError, ValueError, OverflowError, OSError):
                    timestamp = ""

                # Compatibility fallback for older deployments without `timestamp`.
                if not timestamp:
                    timestamp = str(item.get("time") or "")

                self.chat_text.insert("end", sender, "sender")
                if timestamp:
                    self.chat_text.insert("end", "  " + timestamp + "\n", "time")
                else:
                    self.chat_text.insert("end", "\n", "time")
                self.chat_text.insert("end", message + "\n\n", "message")
            self.chat_text.configure(state="disabled")
            if was_at_bottom:
                self.chat_text.see("end")
        except tk.TclError:
            pass

    def update_chat_status(self, text, color="#aeb8c8"):
        try:
            if self.chat_status_label is not None and self.chat_status_label.winfo_exists():
                self.chat_status_label.config(text=text, fg=color)
            if self.chat_entry is not None and self.chat_entry.winfo_exists():
                self.chat_entry.config(state="normal")
        except tk.TclError:
            pass

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
            self.result_queue.put(("status", f"Verified faction: {faction['name']} (ID {faction['id']})."))
        request_started_mono = time.monotonic()
        # Use Torn's dedicated v2 chain endpoint as the authoritative live source.
        # The previous v1 endpoint was returning a count behind the in-game chain.
        # Torn API v2 uses the canonical /faction/chain route and an `id`
        # query parameter for a specific faction. The /faction/{id}/chain path
        # is not the documented v2 route and can yield stale/unexpected data.
        params = urllib.parse.urlencode({
            "key": api_key,
            "id": str(FACTION_ID),
            "timestamp": str(int(time.time())),
        })
        request = urllib.request.Request(
            f"{API_V2_FACTION_CHAIN_URL}?{params}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache",
            },
        )
        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8-sig"))
        response_received_mono = time.monotonic()
        if not isinstance(data, dict):
            raise ValueError("Unexpected response from Torn API v2 chain endpoint.")
        if "error" in data:
            error = data["error"]
            if isinstance(error, dict):
                raise ValueError(f"API v2 error {error.get('code', '?')}: {error.get('error', error.get('message', 'Unknown error'))}")
            raise ValueError(str(error))
        chain = data.get("chain")
        if not isinstance(chain, dict) or "timeout" not in chain:
            raise ValueError("Response is missing valid chain.timeout.")
        raw_timeout = chain["timeout"]
        if isinstance(raw_timeout, bool):
            raise ValueError("Invalid timeout value.")
        try:
            timeout_value = float(raw_timeout)
        except (TypeError, ValueError):
            raise ValueError("Timeout value is not numeric.")
        if not math.isfinite(timeout_value) or timeout_value < 0:
            raise ValueError("Timeout value is invalid or negative.")

        raw_start = chain.get("start")
        try:
            chain_start = int(raw_start) if raw_start is not None else None
        except (TypeError, ValueError):
            chain_start = None
        if chain_start is not None and chain_start <= 0:
            chain_start = None

        raw_current = chain.get("current")
        try:
            current_value = int(raw_current) if raw_current is not None else None
        except (TypeError, ValueError):
            current_value = None
        if current_value is not None and current_value < 0:
            current_value = None

        raw_chain_current = current_value

        # Read faction attacks from the API v2 endpoint. The older v1 request
        # (api.torn.com/faction/9412?selections=attacks) can fail with a key-access
        # error even when the custom key has the API-v2 faction -> attacks selection.
        latest_success_timestamp = None
        latest_success_chain = None
        attacks_max_chain = None
        attacks_error = None
        try:
            # Use the documented v2 faction-attacks route with explicit faction ID.
            attack_params = urllib.parse.urlencode({
                "key": api_key,
                "id": str(FACTION_ID),
                "limit": "100",
                "sort": "DESC",
                "timestamp": str(int(time.time())),
            })
            attack_request = urllib.request.Request(
                f"{API_V2_FACTION_ATTACKS_URL}?{attack_params}",
                headers={
                    "User-Agent": "BlackStatuesChainTimer/1.0",
                    "Cache-Control": "no-cache",
                    "Pragma": "no-cache",
                },
            )
            with urllib.request.urlopen(attack_request, timeout=REQUEST_TIMEOUT) as response:
                attack_data = json.loads(response.read().decode("utf-8-sig"))

            if not isinstance(attack_data, dict):
                raise ValueError("API v2 attacks response was not an object.")
            if "error" in attack_data:
                err = attack_data["error"]
                if isinstance(err, dict):
                    attacks_error = str(err.get("error") or err.get("message") or err)
                else:
                    attacks_error = str(err)
            else:
                attacks = attack_data.get("attacks", [])
                # API v2 normally returns a list; accept a dictionary too, in case
                # Torn changes/serves a keyed representation.
                if isinstance(attacks, dict):
                    attack_items = list(attacks.values())
                elif isinstance(attacks, list):
                    attack_items = attacks
                else:
                    attack_items = []
                    attacks_error = "API v2 response has no usable attacks list."

                candidates = []
                for attack in attack_items:
                    if not isinstance(attack, dict):
                        continue
                    try:
                        chain_number = int(attack.get("chain") or 0)
                        # API v2 fields are 'ended' and 'started'; API v1 used
                        # 'timestamp_ended' and 'timestamp_started'.
                        ended = int(
                            attack.get("ended")
                            or attack.get("timestamp_ended")
                            or attack.get("started")
                            or attack.get("timestamp_started")
                            or 0
                        )
                    except (TypeError, ValueError):
                        continue

                    if chain_number > 0 and ended > 0:
                        if chain_start is None or ended >= chain_start:
                            candidates.append((ended, chain_number))

                if candidates:
                    latest_success_timestamp, latest_success_chain = max(candidates)
                    attacks_max_chain = max(chain_number for _, chain_number in candidates)
                elif not attacks_error:
                    attacks_error = "API v2 returned no qualifying chain attacks."

        except urllib.error.HTTPError as exc:
            # Include Torn's response body when available; it often explains whether
            # the key is missing a selection or the endpoint/parameters are invalid.
            try:
                body = exc.read().decode("utf-8", errors="replace")[:300]
            except Exception:
                body = ""
            attacks_error = f"HTTP {exc.code}: {body or exc.reason}"
        except Exception as exc:
            attacks_error = str(exc)

        # Reconcile the live v2 chain.current value against the highest
        # successful attack count observed since this chain began.
        if attacks_max_chain is not None:
            if current_value is None or attacks_max_chain > current_value:
                current_value = attacks_max_chain

        return {
            "timeout": timeout_value,
            "current": current_value,
            "raw_chain_current": raw_chain_current,
            "chain_start": chain_start,
            "latest_success_timestamp": latest_success_timestamp,
            "latest_success_chain": latest_success_chain,
            "attacks_max_chain": attacks_max_chain,
            "attacks_error": attacks_error,
            "request_started_mono": request_started_mono,
            "response_received_mono": response_received_mono,
        }

    def refresh_api(self):
        if self.key_validation_in_progress:
            self.set_message("Please wait for API key verification to finish.")
            return
        threading.Thread(target=self.api_request_worker, daemon=True).start()

    def api_request_worker(self):
        if not self.request_lock.acquire(blocking=False):
            return
        try:
            self.result_queue.put(("success", self.fetch_chain_data()))
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
            self.set_message("Enter and verify your API key to start polling.")
            return
        self.polling = True
        self.poll_stop_event.clear()
        threading.Thread(target=self.polling_worker, daemon=True).start()
        self.set_message("Automatic API polling started (every 5 seconds).")

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
                    raw_count = value.get("raw_chain_current")
                    attacks_count = value.get("attacks_max_chain")
                    merged_count = value.get("current")
                    displayed_count = self.last_chain_current
                    self.chain_api_debug_label.config(
                        text=(
                            f"API timeout={value.get('timeout', '—')} | "
                            f"chain.current={raw_count if raw_count is not None else '—'} | "
                            f"attacks max={attacks_count if attacks_count is not None else '—'} | "
                            f"merged={merged_count if merged_count is not None else '—'} | "
                            f"shown={displayed_count if displayed_count is not None else '—'} | "
                            f"attack ts={value.get('latest_success_timestamp') if value.get('latest_success_timestamp') is not None else '—'} | "
                            f"attack chain={value.get('latest_success_chain') if value.get('latest_success_chain') is not None else '—'} | "
                            f"attacks error={(str(value.get('attacks_error') or 'none'))[:55]}"
                        )
                    )
                elif kind == "error":
                    message = f"API request failed: {value}"
                    if self.polling:
                        message += ". Retrying automatically."
                    self.set_message(message)
                elif kind == "status":
                    self.set_message(value)
                elif kind == "players_success":
                    self.handle_players_success(value)
                elif kind == "players_error":
                    self.players_message = f"Players error: {value}"
                    self.update_players_label()
                elif kind == "online_success":
                    self.online_refresh_in_progress = False
                    self.update_online_window(value)
                elif kind == "online_error":
                    self.online_refresh_in_progress = False
                    self.update_online_error(value)
                elif kind == "online_presence_status":
                    self.update_online_presence_status(value)
                elif kind == "chat_success":
                    self.chat_request_in_progress = False
                    self.update_chat_messages(value)
                    self.update_chat_status("Connected • refreshes every 5 seconds", "#63e68b")
                elif kind == "chat_send_success":
                    self.chat_request_in_progress = False
                    self.update_chat_status("Message sent", "#63e68b")
                    self.refresh_chat()
                elif kind == "chat_error":
                    self.chat_request_in_progress = False
                    self.update_chat_status("Chat error: " + str(value), "#ff9c9c")
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

    def reset_spoken_countdown_if_new(self, proposed_deadline_wall):
        if self.deadline is None or abs(proposed_deadline_wall - self.deadline) > 10:
            self.speech_deadline = proposed_deadline_wall
            self.spoken_milestones.clear()
            self.last_speech_remaining = None
            self.one_minute_failsafe_sent = False

    def apply_api_timeout(self, result):
        """Synchronize from chain.timeout using a monotonic clock.

        API latency is accounted for by subtracting the time spent waiting for
        the response. Every successful poll updates the deadline, even when the
        timeout number is unchanged, preventing stale deadlines.
        """
        received_mono = result.get("response_received_mono", time.monotonic())
        timeout_value = float(result["timeout"])
        current_value = result.get("current")
        now_mono = time.monotonic()
        # Preserve the time of the previous successful API report before updating it.
        # If the chain count has increased, the hit happened sometime between that
        # previous report and this detection, so account for that whole interval.
        previous_api_report_mono = self.last_success_monotonic
        self.last_success_monotonic = now_mono
        self.last_api_timeout_received = timeout_value
        self.last_api_end_received = None

        # Detect a new successful hit by the chain counter increasing.
        # Torn can return an older cached chain.current value after a newer one.
        # Never let such a lower report roll the displayed counter backwards or
        # replace the highest count already observed during the active chain.
        # The counter may reset only when the API confirms the chain is inactive
        # (timeout == 0); otherwise keep the higher observed count.
        previous_chain_current = self.last_chain_current
        chain_start = result.get("chain_start")
        if isinstance(chain_start, (int, float)) and chain_start > 0:
            if self.last_chain_start is not None and chain_start != self.last_chain_start:
                # A different chain has started; do not carry the prior chain's
                # hit count or attack timestamp into the new chain.
                self.last_chain_current = None
                self.last_success_attack_timestamp = None
                self.last_success_attack_chain = None
                previous_chain_current = None
            self.last_chain_start = chain_start

        latest_attack_ts = result.get("latest_success_timestamp")
        latest_attack_chain = result.get("latest_success_chain")
        previous_attack_ts = self.last_success_attack_timestamp

        # Prefer the timestamped faction-attacks feed: it can detect the latest
        # successful hit even when chain.current skips several intermediate counts.
        attack_age_for_validation = (
            max(0.0, time.time() - float(latest_attack_ts))
            if isinstance(latest_attack_ts, (int, float)) and latest_attack_ts > 0
            else None
        )
        attack_timestamp_is_new = (
            isinstance(latest_attack_ts, (int, float))
            and latest_attack_ts > 0
            and previous_attack_ts is not None
            and latest_attack_ts > previous_attack_ts
            and attack_age_for_validation is not None
            and attack_age_for_validation <= CHAIN_TIMEOUT_SECONDS
            and float(latest_attack_ts) <= time.time() + 5.0
        )
        # On first startup, establish a baseline without treating an old attack
        # already present in the feed as a newly detected hit.
        if self.last_success_attack_timestamp is None and isinstance(latest_attack_ts, (int, float)) and latest_attack_ts > 0:
            self.last_success_attack_timestamp = latest_attack_ts
            self.last_success_attack_chain = latest_attack_chain
        elif attack_timestamp_is_new:
            self.last_success_attack_timestamp = latest_attack_ts
            self.last_success_attack_chain = latest_attack_chain

        count_increased = (
            current_value is not None
            and previous_chain_current is not None
            and current_value > previous_chain_current
        )
        hit_detected = attack_timestamp_is_new or count_increased
        # Zero timeout without a new count/timestamp is ambiguous, not proof of expiry.
        self.chain_state_unconfirmed = bool(timeout_value <= 0 and not hit_detected)
        if hit_detected or timeout_value > 0:
            self.chain_state_unconfirmed = False

        if current_value is not None:
            if previous_chain_current is None:
                self.last_chain_current = current_value
            elif current_value >= previous_chain_current:
                self.last_chain_current = current_value
            elif timeout_value <= 0:
                self.last_chain_current = current_value
            # Otherwise ignore stale lower values for display/hit detection.

        request_started_mono = result.get("request_started_mono", received_mono)
        if not isinstance(request_started_mono, (int, float)):
            request_started_mono = received_mono
        request_elapsed = max(0.0, now_mono - float(request_started_mono))
        if (previous_api_report_mono is not None
                and isinstance(previous_api_report_mono, (int, float))):
            elapsed_since_previous_report = max(0.0, now_mono - float(previous_api_report_mono))
        else:
            elapsed_since_previous_report = request_elapsed

        if hit_detected:
            # A rising chain count is positive evidence of a successful hit even
            # when Torn's chain endpoint incorrectly reports timeout=0. In that
            # case, start the 5-minute timer from the newly observed hit/count
            # change rather than immediately expiring the countdown. Subtract the
            # interval since the previous successful poll to avoid granting extra time.
            if timeout_value <= 0:
                timeout_value = float(CHAIN_TIMEOUT_SECONDS)
            else:
                timeout_value = float(CHAIN_TIMEOUT_SECONDS)
            self.last_api_timeout_received = float(result["timeout"])

        # Startup recovery: a newly opened app has no local deadline to compare
        # against. If the chain endpoint incorrectly/stalely reports timeout=0
        # but the attacks feed contains a successful chain hit within the last
        # five minutes, rebuild the countdown from that attack timestamp instead
        # of immediately declaring the active chain expired.
        startup_recovered_from_attack = False
        latest_attack_timestamp = result.get("latest_success_timestamp")
        if ((self.deadline_mono is None or self.startup_sync_pending) and timeout_value <= 0
                and isinstance(latest_attack_timestamp, (int, float))
                and latest_attack_timestamp > 0):
            attack_age = max(0.0, time.time() - float(latest_attack_timestamp))
            if attack_age < CHAIN_TIMEOUT_SECONDS:
                timeout_value = max(0.0, float(CHAIN_TIMEOUT_SECONDS) - attack_age)
                self.last_api_timeout_received = float(result["timeout"])
                startup_recovered_from_attack = True
                self.set_message(
                    "Startup recovery: chain API reported 0, but a recent successful "
                    "chain hit was found; rebuilding timer from its timestamp."
                )

        # During startup, do not let a stale or implausibly short API timeout
        # replace the 10:00 synchronization countdown. This is the observed
        # failure mode: the display starts correctly, then a cached 0-14 second
        # timeout overwrites it and immediately triggers the flatline.
        # A confirmed count/timestamp increase or a recent successful attack
        # recovered above is still allowed to synchronize the timer.
        if (self.startup_sync_pending
                and not hit_detected
                and not startup_recovered_from_attack
                and timeout_value < 15.0):
            self.chain_state_unconfirmed = True
            self.set_message(
                f"Startup sync still pending: ignored suspicious Torn timeout "
                f"{int(max(0.0, timeout_value))}s; keeping the 10:00 grace countdown "
                "until a usable timer or confirmed new hit is received."
            )
            return

        if timeout_value > 0 or hit_detected or startup_recovered_from_attack:
            self.chain_state_unconfirmed = False

        if self.last_timeout_value is None or timeout_value != self.last_timeout_value or hit_detected or startup_recovered_from_attack:
            self.last_timeout_value = timeout_value
            self.last_timeout_change_monotonic = now_mono

        if hit_detected and isinstance(latest_attack_ts, (int, float)) and latest_attack_ts > 0 and attack_timestamp_is_new:
            # Use the actual successful-attack end timestamp, not the time at which
            # the polling loop finally noticed it. This handles several hits arriving
            # between reports and avoids granting a fresh 5:00 at late detection.
            hit_age_seconds = max(0.0, time.time() - float(latest_attack_ts))
            proposed_deadline_mono = now_mono + max(0.0, float(CHAIN_TIMEOUT_SECONDS) - hit_age_seconds)
        elif hit_detected:
            # Fallback when the attacks feed is unavailable: subtract the elapsed
            # time since the previous successful poll.
            proposed_deadline_mono = now_mono + max(0.0, timeout_value - elapsed_since_previous_report)
        else:
            proposed_deadline_mono = received_mono + timeout_value
        proposed_deadline_wall = time.time() + max(0.0, proposed_deadline_mono - now_mono)

        # Process every successful API report, but don't blindly trust it to
        # replace the local deadline: Torn may briefly return a stale timeout.
        # A report is considered safe to reconcile only when its remaining time
        # is close to our local estimate. A new chain.current value is the only
        # signal that authorizes a fresh five-minute anchor.
        if (not hit_detected and self.deadline_mono is not None
                and not self.startup_sync_pending):
            local_remaining = max(0.0, self.deadline_mono - now_mono)
            api_remaining_now = max(0.0, received_mono + float(result["timeout"]) - now_mono)
            discrepancy = abs(api_remaining_now - local_remaining)

            # Ignore a zero/expired report if our local timer still has meaningful
            # time remaining; it may be an older cached response. If both clocks
            # are near expiry, allow the normal expiry handling below.
            if timeout_value <= 0 and local_remaining > 15.0:
                self.set_message(
                    f"API reports expired chain, but local countdown has "
                    f"{int(local_remaining)//60}:{int(local_remaining)%60:02d}; "
                    "possible stale report ignored."
                )
                return

            # Accept useful API updates when they agree within 15 seconds. Larger
            # gaps are treated as stale/inconsistent; the report is still consumed
            # for chain-count and timing baselines above, so later hits are detected.
            if discrepancy > 15.0:
                self.set_message(
                    f"API report processed (chain {current_value if current_value is not None else '—'}); "
                    f"API remaining {int(api_remaining_now)//60}:{int(api_remaining_now)%60:02d}, "
                    f"local remaining {int(local_remaining)//60}:{int(local_remaining)%60:02d}. "
                    "Large discrepancy; keeping local countdown to avoid stale resync."
                )
                return

        if timeout_value <= 0:
            # A zero timeout alone is not enough to prove that the live chain is
            # expired. Do not overwrite a local deadline or play the deadline sound
            # unless a real expiry is supported by confirmed data.
            self.stop_alarm()
            if self.deadline_mono is not None:
                local_remaining = self.deadline_mono - now_mono
                if local_remaining > 0:
                    self.set_message(
                        f"Torn API timeout is 0, but chain state is unconfirmed; "
                        f"keeping the local countdown at {int(local_remaining)//60}:"
                        f"{int(local_remaining)%60:02d}. Deadline sound suppressed "
                        "until a new hit or confirmed timer state is received."
                    )
                    return
                # Keep the display at 00:00 once the local countdown has elapsed.
                # The user explicitly wants the startup/local timer to expire audibly
                # even if Torn's API remains stuck at timeout=0.
                self.deadline_mono = min(self.deadline_mono, now_mono)
                self.deadline = time.time()
            self._last_applied_timeout = timeout_value
            self.set_message(
                "Torn API timeout is 0; local countdown is allowed to reach 00:00 "
                "and announce expiry even while chain state is unconfirmed."
            )
            return

        previous_deadline_mono = self.deadline_mono
        self.deadline_mono = proposed_deadline_mono
        self.deadline = proposed_deadline_wall
        self._last_applied_timeout = timeout_value
        # A usable API timer (or a confirmed new hit) has now replaced the
        # temporary 10:00 startup synchronization countdown.
        self.startup_sync_pending = False

        if previous_deadline_mono is None or abs(proposed_deadline_mono - previous_deadline_mono) > 10:
            self.speech_deadline = proposed_deadline_wall
            self.spoken_milestones.clear()
            self.last_speech_remaining = None
            self.one_minute_failsafe_sent = False

        self.failure_sound_played = False
        self.expiry_handled = False
        if self.deadline_mono <= now_mono:
            self.stop_alarm()
            self.play_failure_sound_once()
            self.set_message("The chain timer has expired.")
        else:
            self.set_message(
                (f"New successful hit detected (chain count {current_value}); "
                 f"timer anchored to attack timestamp when available. API timeout was "
                 f"{int(result['timeout'])//60}:{int(result['timeout'])%60:02d}; "
                 f"local timer set to {max(0, int(proposed_deadline_mono - now_mono))//60}:"
                 f"{max(0, int(proposed_deadline_mono - now_mono))%60:02d}."
                 if hit_detected else
                 f"API reports {int(timeout_value)} sec ({int(timeout_value)//60}:{int(timeout_value)%60:02d}); countdown synchronized.")
            )

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
            stale_text, stale_color = "API connection: NOT VERIFIED", "#e9b44c"
        else:
            age = now - self.last_success_monotonic
            if age >= STALE_AFTER_SECONDS:
                stale_text, stale_color = f"WARNING: API CONNECTION STALE ({int(age)}s)", "#ff6262"
            else:
                stale_text, stale_color = "API connection: OK", "#63e68b"
        if self.last_timeout_change_monotonic is None:
            unchanged_text, unchanged_color = "Timeout: waiting for first valid value", "#e9b44c"
        else:
            age = now - self.last_timeout_change_monotonic
            if age >= UNCHANGED_AFTER_SECONDS:
                unchanged_text, unchanged_color = f"WARNING: TIMEOUT UNCHANGED ({int(age)}s)", "#e9b44c"
            else:
                unchanged_text, unchanged_color = f"Timeout: last changed {int(age)}s ago", "#63e68b"
        self.normal_stale_label.config(text=stale_text, fg=stale_color)
        self.compact_stale_label.config(text=stale_text, fg=stale_color)
        self.normal_unchanged_label.config(text=unchanged_text, fg=unchanged_color)
        self.compact_unchanged_label.config(text=unchanged_text, fg=unchanged_color)

    def update_chain_milestone_warning(self):
        """Show a centered warning during the last 20 hits before each milestone."""
        count = self.last_chain_current
        warning_text = ""
        if isinstance(count, (int, float)):
            count = int(count)
            for milestone in CHAIN_HIT_WARNING_MILESTONES:
                hits_remaining = milestone - count
                if 1 <= hits_remaining <= CHAIN_HIT_WARNING_LEAD:
                    warning_text = (
                        f"⚠ WATCH FACTION CHAT — HIT #{milestone:,} IN "
                        f"{hits_remaining} HIT{'S' if hits_remaining != 1 else ''} ⚠"
                    )
                    break

        if warning_text:
            self.chain_milestone_warning_label.config(text=warning_text)
            if not self.chain_milestone_warning_visible:
                self.chain_milestone_warning_label.pack(
                    fill="x", pady=(1, 2), after=self.countdowns_row
                )
                self.chain_milestone_warning_visible = True
                # Speak once when a milestone warning first triggers, not on every UI refresh.
                self.speak("Watch faction chat")
        elif self.chain_milestone_warning_visible:
            self.chain_milestone_warning_label.pack_forget()
            self.chain_milestone_warning_visible = False

    def update_display(self):
        now_mono = time.monotonic()
        remaining = None
        if self.deadline_mono is not None:
            remaining = max(0, int(math.ceil(self.deadline_mono - now_mono)))
        if remaining is not None:
            self.announce_countdown_milestones(remaining)
            if 0 < remaining <= 60 and not self.one_minute_failsafe_sent:
                self.one_minute_failsafe_sent = True
                self.send_one_minute_failsafe()
        timer_text = "--:--" if remaining is None else f"{remaining // 60:02d}:{remaining % 60:02d}"
        color = "#FF3333"
        if remaining is not None and remaining <= 60:
            if now_mono - self.last_flash_toggle >= 0.5:
                self.flash_visible = not self.flash_visible
                self.last_flash_toggle = now_mono
            color = "#ff4d4d" if self.flash_visible else "#17191f"
        self.timer_label.config(text=timer_text, fg=color)
        self.compact_timer_label.config(text=timer_text, fg=color)
        if self.last_chain_current is None:
            self.chain_hits_label.config(text="—")
        else:
            # Format counts with comma separators, e.g. 39,475 / 100,000.
            self.chain_hits_label.config(text=f"{self.last_chain_current:,}")
        self.update_chain_milestone_warning()
        self.update_warning_labels(now_mono)
        if remaining is not None and 0 < remaining <= ALARM_START_SECONDS:
            self.start_alarm()
        if remaining is not None and remaining <= 0:
            self.stop_alarm()
            if not self.expiry_handled:
                # Keep 00:00 visible and play/speak expiry once, even if the API
                # cannot confirm the chain state. A later usable timer or new hit
                # resets this flag and starts a fresh countdown.
                self.expiry_handled = True
                self.play_failure_sound_once()
                # announce_countdown_milestones() above already speaks the expiry.
                self.set_message(
                    "Countdown expired at 00:00. Expiry sound and announcement triggered. "
                    "Torn API chain state may still be unconfirmed."
                )
        try:
            self.root.after(200, self.update_display)
        except tk.TclError:
            pass

    # --------------------------------------------------------
    # SPOKEN COUNTDOWN ANNOUNCEMENTS
    # --------------------------------------------------------

    def speak(self, phrase):
        if os.name != "nt":
            return
        escaped_phrase = phrase.replace("'", "''")
        powershell_script = (
            "Add-Type -AssemblyName System.Speech; "
            "$voice = New-Object System.Speech.Synthesis.SpeechSynthesizer; "
            f"$voice.Speak('{escaped_phrase}'); "
            "$voice.Dispose()"
        )
        try:
            creation_flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            subprocess.Popen(
                ["powershell.exe", "-NoLogo", "-NoProfile", "-NonInteractive",
                 "-ExecutionPolicy", "Bypass", "-Command", powershell_script],
                stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                creationflags=creation_flags, close_fds=True
            )
        except Exception as exc:
            print("Speech announcement could not start:", exc)

    def announce_countdown_milestones(self, remaining):
        if self.deadline_mono is None:
            return
        if self.speech_deadline is None:
            self.speech_deadline = self.deadline
        if self.last_speech_remaining is None:
            if remaining <= 0:
                self.spoken_milestones.update((60, 40, 20))
            elif remaining <= 60:
                upcoming = next((m for m in (20, 40, 60) if remaining <= m), None)
                if upcoming is not None:
                    for milestone in (60, 40, 20):
                        if milestone > upcoming:
                            self.spoken_milestones.add(milestone)
                    if upcoming not in self.spoken_milestones:
                        self.speak({60: "One minute remaining.", 40: "Forty seconds remaining.",
                                    20: "Twenty seconds remaining."}[upcoming])
                        self.spoken_milestones.add(upcoming)
            self.last_speech_remaining = remaining
            if remaining <= 0 and 0 not in self.spoken_milestones:
                self.speak("Chain timeout expired.")
                self.spoken_milestones.add(0)
            return
        for milestone, phrase in (
            (60, "One minute remaining."), (40, "Forty seconds remaining."),
            (20, "Twenty seconds remaining.")
        ):
            if (milestone not in self.spoken_milestones
                    and self.last_speech_remaining > milestone
                    and remaining <= milestone and remaining > 0):
                self.speak(phrase)
                self.spoken_milestones.add(milestone)
        if remaining <= 0 and 0 not in self.spoken_milestones:
            self.speak("Chain timeout expired.")
            self.spoken_milestones.add(0)
        self.last_speech_remaining = remaining

    # --------------------------------------------------------
    # ALARM SOUNDS
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
            deadline = self.deadline_mono
            if deadline is None:
                return
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return
            try:
                if winsound is not None:
                    if remaining <= 20:
                        winsound.Beep(FINAL_BEEP_FREQUENCY, FINAL_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.04):
                            return
                        winsound.Beep(FINAL_BEEP_FREQUENCY - 300, 120)
                        pause = FINAL_BEEP_PAUSE_MS / 1000.0
                    elif remaining <= 40:
                        winsound.Beep(NORMAL_BEEP_FREQUENCY, NORMAL_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.10):
                            return
                        winsound.Beep(NORMAL_BEEP_FREQUENCY - 200, 180)
                        pause = NORMAL_BEEP_PAUSE_MS / 1000.0
                    elif remaining <= 60:
                        winsound.Beep(SLOW_BEEP_FREQUENCY, SLOW_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.12):
                            return
                        winsound.Beep(SLOW_BEEP_FREQUENCY - 180, 180)
                        pause = SLOW_BEEP_PAUSE_MS / 1000.0
                    else:
                        pause = 0.05
                else:
                    pause = 0.2
            except Exception:
                pause = 0.2
            if self.alarm_stop_event.wait(pause):
                return

    def play_failure_sound_once(self):
        if self.failure_sound_played:
            return
        self.failure_sound_played = True
        self.stop_alarm()
        if winsound is None:
            return
        def play_flatline():
            try:
                winsound.Beep(FAILURE_BEEP_FREQUENCY, FAILURE_BEEP_DURATION_MS)
            except Exception as exc:
                print("Flatline sound could not play:", exc)
        threading.Thread(target=play_flatline, daemon=True).start()

    # --------------------------------------------------------
    # CLOSE
    # --------------------------------------------------------

    def close_app(self):
        self.polling = False
        self.poll_stop_event.set()
        self.players_poll_stop_event.set()
        self.online_presence_stop_event.set()
        self.send_offline_presence()
        self.close_online_window()
        self.close_chat_window()
        self.stop_alarm()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = ChainTimerApp(root)
    root.mainloop()
