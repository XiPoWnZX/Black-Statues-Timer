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

APP_NAME = "Black Statues Chain T"
FACTION_ID = 9412

API_URL = f"https://api.torn.com/faction/{FACTION_ID}"
VERIFY_API_URL = "https://api.torn.com/v2/user/faction"

POLL_INTERVAL = 5
PLAYERS_POLL_INTERVAL = 300

# Google Apps Script connection (set these two values once, here in the code).
# Deploy the Apps Script as a Web App, then paste its /exec URL below.
PLAYERS_WEB_APP_URL = "https://script.google.com/macros/s/AKfycbzjyFI9rq7DYp7EI3GuU5kWEN8M9DEM-sqqOT4MPW3H9LxoQum1sh9L7j8A4e9-vJskBw/exec"
# Must exactly match the PLAYERS_API_TOKEN value in Apps Script Properties.
PLAYERS_API_TOKEN = "c887e4b71b2fb5ea233d752950c94161bb5965a15db2fea719be3ff78755e486"

# Shared Discord webhook for the packaged faction app. Paste your webhook URL here locally.
DISCORD_WEBHOOK_URL = "https://discord.com/api/webhooks/1564803004463448077/lXmKIp_wLrZ6K6WgXC2k5PQ-XxCqYpFb9dNG7Bz65y7NjAmoQf9ssTB4JLXF8RrU5lGg"
# Separate webhook for the automatic 1-minute failsafe alert (the other Discord channel).
ONE_MINUTE_FAILSAFE_WEBHOOK_URL = "https://discord.com/api/webhooks/1564803116753231982/_QZTxsJgWwF0Rofb1f1VoLJNq9Q4dvxNWqwRWXFH09gkC4mbl_dPiYJtxJtrYZdspxUh"
ONE_MINUTE_FAILSAFE_ROLE_ID = "417878002181996544"

REQUEST_TIMEOUT = 10
STALE_AFTER_SECONDS = 20
UNCHANGED_AFTER_SECONDS = 60

NORMAL_WIDTH = 360
NORMAL_HEIGHT = 310
COMPACT_WIDTH = 180
COMPACT_HEIGHT = 110
SCREEN_MARGIN = 10

# Heartbeat starts at 60 seconds remaining.
ALARM_START_SECONDS = 60

# True = run the 70-second sound test. Set to False for live Torn API mode.
TEST_MODE = False

# Slower heartbeat from 60 to 41 seconds remaining
SLOW_BEEP_FREQUENCY = 1000
SLOW_BEEP_DURATION_MS = 180
SLOW_BEEP_PAUSE_MS = 350

# Normal heartbeat from 40 to 21 seconds remaining
NORMAL_BEEP_FREQUENCY = 1200
NORMAL_BEEP_DURATION_MS = 120
NORMAL_BEEP_PAUSE_MS = 160

# Faster heartbeat during the final 20 seconds
FINAL_BEEP_FREQUENCY = 1800
FINAL_BEEP_DURATION_MS = 100
FINAL_BEEP_PAUSE_MS = 40

# Flatline sound at expiry: one steady tone for 8 seconds
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
        self.one_minute_failsafe_sent = False

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

        self.update_display()
        self.process_queue()
        self.root.after(700, self.start_players_polling)

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

    def call_for_help(self):
        """Send the fixed help message and notify only the configured Discord role."""
        webhook_url = DISCORD_WEBHOOK_URL.strip()
        if (not webhook_url.startswith("https://discord.com/api/webhooks/")
                and not webhook_url.startswith("https://discordapp.com/api/webhooks/")):
            messagebox.showerror(
                "Discord Webhook Not Configured",
                "The shared Discord webhook has not been configured yet.\n\n"
                "Open this Python file and replace PASTE_YOUR_DISCORD_WEBHOOK_URL_HERE "
                "in DISCORD_WEBHOOK_URL with your webhook URL, then package the app.",
                parent=self.root
            )
            return

        if not messagebox.askyesno(
            "Call for Help",
            "Send a CALL FOR HELP alert to Discord now?",
            parent=self.root
        ):
            return

        threading.Thread(
            target=self.call_for_help_worker,
            args=(webhook_url,),
            daemon=True
        ).start()
        self.set_message("Sending Discord help alert...")

    def call_for_help_worker(self, webhook_url):
        role_id = "626217573406474296"
        payload = {
            "content": f"<@&{role_id}> Help needed!",
            "allowed_mentions": {
                "parse": [],
                "roles": [role_id]
            }
        }
        try:
            request = urllib.request.Request(
                webhook_url,
                data=json.dumps(payload).encode("utf-8"),
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
        """Send the one-minute warning once for the current countdown."""
        webhook_url = ONE_MINUTE_FAILSAFE_WEBHOOK_URL.strip()
        if (not webhook_url.startswith("https://discord.com/api/webhooks/")
                and not webhook_url.startswith("https://discordapp.com/api/webhooks/")):
            self.set_message("1-minute failsafe not sent: second Discord webhook is not configured.")
            return

        role_id = ONE_MINUTE_FAILSAFE_ROLE_ID
        payload = {
            "content": f"<@&{role_id}> ⚠️ CHAIN TIMER FAILSAFE: 1 minute remaining!",
            "allowed_mentions": {"parse": [], "roles": [role_id]}
        }
        threading.Thread(
            target=self.one_minute_failsafe_worker,
            args=(webhook_url, payload),
            daemon=True
        ).start()

    def one_minute_failsafe_worker(self, webhook_url, payload):
        try:
            request = urllib.request.Request(
                webhook_url,
                data=json.dumps(payload).encode("utf-8"),
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
                "API Key", "The API key cannot be empty.", parent=self.root
            )
            return

        self.set_message("Verifying API key and faction membership...")
        self.key_validation_in_progress = True
        threading.Thread(
            target=self.validate_key_worker, args=(new_key,), daemon=True
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
                "Make sure the key has access to user → faction information "
                "and that its owner is currently in a faction."
            )

        try:
            faction_id = int(faction.get("id"))
        except (TypeError, ValueError):
            raise ValueError("Torn returned an invalid faction ID.")

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
                "api_key": api_key, "faction": faction
            }))
        except urllib.error.HTTPError as exc:
            self.result_queue.put((
                "key_validation_error", f"HTTP error {exc.code}: {exc.reason}"
            ))
        except urllib.error.URLError as exc:
            self.result_queue.put((
                "key_validation_error", f"Network error: {exc.reason}"
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
            "The API key could not be verified for BLACK STATUES.\n\n"
            f"{error}\n\nThe new key was not saved.",
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
        # Let the user choose an opacity from 60% through 100%.
        current_alpha = float(self.root.attributes("-alpha"))
        current_percent = max(60, min(100, round(current_alpha * 100)))
        selected_percent = simpledialog.askinteger(
            "Window Transparency",
            "Choose window opacity (60–100):",
            initialvalue=current_percent,
            minvalue=60,
            maxvalue=100,
            parent=self.root,
        )
        # Cancel closes the dialog without changing the current opacity.
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

        # Right-side controls are stacked: lock first, opacity toggle directly below.
        normal_top_controls = tk.Frame(normal_top, bg=bg)
        normal_top_controls.pack(side="right", anchor="ne")
        self.normal_lock_button = tk.Button(
            normal_top_controls, text="🔓", command=self.toggle_lock,
            font=("Segoe UI Emoji", 9), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=3, padx=0, pady=0, cursor="hand2"
        )
        self.normal_lock_button.pack(side="top", anchor="e")
        self.transparency_button = tk.Button(
            normal_top_controls, text="85%", command=self.toggle_transparency,
            font=("Segoe UI", 7, "bold"), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=4, padx=0, pady=1, cursor="hand2"
        )
        self.transparency_button.pack(side="top", anchor="e", pady=(2, 0))

        self.timer_label = tk.Label(
            self.normal_frame, text="--:--", font=("Consolas", 32, "bold"),
            fg="#63e68b", bg=bg, anchor="center"
        )
        self.timer_label.pack(fill="x")

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
        self.normal_unchanged_label.pack(fill="x", pady=(1, 3))

        # Guard roster: center the complete "Guards : names" group in the window.
        # The heading stays on the left and the player names appear immediately to its right.
        self.players_row = tk.Frame(self.normal_frame, bg=bg)
        self.players_row.pack(fill="x", pady=(3, 5))

        self.players_content = tk.Frame(self.players_row, bg=bg)
        self.players_content.pack(anchor="center")

        self.players_heading = tk.Label(
            self.players_content, text="Guards :",
            font=("Segoe UI", 9, "bold"), fg="#8fc7ff", bg=bg,
            anchor="e", justify="right"
        )
        self.players_heading.grid(row=0, column=0, padx=(0, 8), sticky="e")

        self.players_list_frame = tk.Frame(self.players_content, bg=bg)
        self.players_list_frame.grid(row=0, column=1, sticky="w")
        self.players_label = tk.Label(
            self.players_list_frame, text=self.players_message,
            font=("Segoe UI", 9), fg="white", bg=bg,
            anchor="w", justify="left", wraplength=225
        )
        self.players_label.pack(anchor="w")
        self.players_content.grid_columnconfigure(0, weight=0)
        self.players_content.grid_columnconfigure(1, weight=0)
        self.players_content.grid_rowconfigure(0, weight=0)

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

        
        self.normal_help_button = tk.Button(
            self.normal_frame,
            text="CALL FOR HELP",
            command=self.call_for_help,
            font=("Segoe UI", 10, "bold"),
            fg="white",
            bg="#a83232",
            activebackground="#c74444",
            activeforeground="white",
            relief="flat",
            bd=0,
            padx=8,
            pady=8,
            height=2,
            cursor="hand2"
        )

        self.normal_help_button.pack(side="bottom", fill="x", expand=False, pady=(2, 0))

        self.compact_frame = tk.Frame(self.root, bg=bg, padx=6, pady=3)
        compact_top = tk.Frame(self.compact_frame, bg=bg)
        compact_top.pack(fill="x")

        # Keep the return-to-normal button on the left and the lock on the right,
        # matching the normal window's lock position.
        self.expand_button = tk.Button(
            compact_top, text="↗", command=self.toggle_countdown_mode,
            font=("Segoe UI", 10, "bold"), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
            relief="flat", bd=0, width=2, padx=0, pady=0, cursor="hand2"
        )
        self.expand_button.pack(side="left")
        self.compact_lock_button = tk.Button(
            compact_top, text="🔓", command=self.toggle_lock,
            font=("Segoe UI Emoji", 8), fg="white", bg="#353944",
            activebackground="#505666", activeforeground="white",
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
            self.normal_unchanged_label, self.players_row, self.players_content, self.players_heading, self.players_label,
            self.compact_frame, compact_top,
            self.compact_title, self.compact_timer_label,
            self.compact_stale_label, self.compact_unchanged_label
        ]
        for widget in drag_widgets:
            widget.bind("<ButtonPress-1>", self.start_drag)
            widget.bind("<B1-Motion>", self.drag_window)
        self.update_lock_buttons()

    # --------------------------------------------------------
    # MODE SWITCHING AND DRAGGING
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

            # Recalculate the full height after restoring normal widgets.
            self.root.update_idletasks()
            required_height = self.normal_frame.winfo_reqheight()
            normal_height = max(NORMAL_HEIGHT, required_height) + 10
            self.position_top_right(NORMAL_WIDTH, normal_height)

            self.root.attributes("-topmost", True)

            # Preserve the selected transparency.
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
        """Open the guard's Torn profile in the default browser."""
        if str(player_id).isdigit() and int(player_id) > 0:
            webbrowser.open(f"https://www.torn.com/profiles.php?XID={int(player_id)}")

    def update_players_label(self):
        try:
            # Rebuild the roster as individual clickable labels.
            for widget in self.player_name_widgets:
                widget.destroy()
            self.player_name_widgets = []

            if self.player_entries:
                self.players_label.pack_forget()
                for index, player in enumerate(self.player_entries):
                    name = player.get("name", "").strip()
                    player_id = str(player.get("id", "")).strip()
                    if not name:
                        continue
                    if player_id.isdigit() and int(player_id) > 0:
                        widget = tk.Label(
                            self.players_list_frame, text=name,
                            font=("Segoe UI", 9, "underline"), fg="#75baff",
                            bg=self.players_content.cget("bg"), cursor="hand2",
                            anchor="w", justify="left", wraplength=225
                        )
                        widget.bind(
                            "<Button-1>",
                            lambda event, pid=player_id: self.open_torn_profile(pid)
                        )
                    else:
                        widget = tk.Label(
                            self.players_list_frame, text=name,
                            font=("Segoe UI", 9), fg="white",
                            bg=self.players_content.cget("bg"),
                            anchor="w", justify="left", wraplength=225
                        )
                    widget.pack(anchor="w")
                    self.player_name_widgets.append(widget)

                # Keep the window where the user left it.
                # Guard roster refreshes must not reposition the window.
            else:
                self.players_label.config(text=self.players_message)
                self.players_label.pack(anchor="w")
                # Do not reposition the window when the guard list is empty.
            self.root.update_idletasks()
        except (tk.TclError, AttributeError):
            pass

    def extract_player_entries(self, data):
        """Read player IDs and names from the On Duty endpoint response."""
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
        """Fetch checked player names from the token-protected Apps Script endpoint."""
        url = PLAYERS_WEB_APP_URL.strip()
        token = PLAYERS_API_TOKEN.strip()
        if (not url or "PASTE_YOUR_DEPLOYED_APPS_SCRIPT_EXEC_URL_HERE" in url
                or not url.startswith("https://script.google.com/macros/s/")):
            raise ValueError("Set PLAYERS_WEB_APP_URL in the Python file to your deployed Apps Script /exec URL.")
        if not token:
            raise ValueError("Set PLAYERS_API_TOKEN in the Python file to the same token stored in Apps Script Properties.")

        separator = "&" if "?" in url else "?"
        query = urllib.parse.urlencode({
            "token": token,
            "_ts": str(int(time.time()))
        })
        request = urllib.request.Request(
            f"{url}{separator}{query}",
            headers={
                "User-Agent": "BlackStatuesChainTimer/1.0",
                "Cache-Control": "no-cache",
                "Pragma": "no-cache"
            }
        )
        with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
            data = json.loads(response.read().decode("utf-8-sig"))
        # The expected endpoint is the On Duty row-2 endpoint. An old deployment
        # can return a different error shape; explain that this is a deployment mismatch.
        if isinstance(data, dict):
            message = str(data.get("message") or data.get("error") or "")
            if data.get("ok") is False and "Unauthorized" in message:
                raise ValueError(
                    "The URL is still serving an OLD Apps Script deployment (its response says "
                    "Unauthorized). In Apps Script, update the Web app deployment to the latest "
                    "code, then test the same /exec URL again."
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
                or not PLAYERS_API_TOKEN.strip()
                ):
            self.players_message = "Set the Apps Script URL and token in the Python file"
            self.update_players_label()
            return
        threading.Thread(target=self.players_request_worker, daemon=True).start()

    def players_request_worker(self):
        try:
            names = self.fetch_players()
            self.result_queue.put(("players_success", names))
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
        if players:
            self.players_message = f"{len(players)} checked player(s)"
        else:
            self.players_message = "No players found in On Duty row 2"
        self.update_players_label()

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
                "status", f"Verified faction: {faction['name']} (ID {faction['id']})."
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

    def reset_spoken_countdown_if_new(self, proposed_deadline):
        if self.deadline is None or abs(proposed_deadline - self.deadline) > 10:
            self.speech_deadline = proposed_deadline
            self.spoken_milestones.clear()
            self.last_speech_remaining = None
            self.one_minute_failsafe_sent = False

    def apply_api_timeout(self, result):
        now_mono = time.monotonic()
        timeout_value = result["timeout"]
        end_value = result["end"]
        self.last_success_monotonic = now_mono

        if self.last_timeout_value is None or timeout_value != self.last_timeout_value:
            self.last_timeout_value = timeout_value
            self.last_timeout_change_monotonic = now_mono

        if timeout_value == 0 and end_value is None:
            self.deadline = 0
            self.stop_alarm()
            self.play_failure_sound_once()
            self.set_message("API reports an inactive or expired chain.")
            return

        proposed_deadline = end_value if end_value is not None else time.time() + timeout_value

        if end_value is not None:
            if self.deadline is not None and abs(end_value - self.deadline) < 1:
                self._last_applied_timeout = timeout_value
                self.set_message("API connected. Countdown synchronized.")
                return
            self.reset_spoken_countdown_if_new(proposed_deadline)
            self.deadline = proposed_deadline
            self._last_applied_timeout = timeout_value
        elif self._last_applied_timeout is None or timeout_value != self._last_applied_timeout:
            self.reset_spoken_countdown_if_new(proposed_deadline)
            self.deadline = proposed_deadline
            self._last_applied_timeout = timeout_value
        else:
            self.set_message("API connected. Timeout unchanged; retrying automatically.")
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

    def update_display(self):
        now_mono = time.monotonic()
        now_wall = time.time()
        remaining = None
        if self.deadline is not None:
            remaining = max(0, int(math.ceil(self.deadline - now_wall)))

        if remaining is not None:
            self.announce_countdown_milestones(remaining)
            if 0 < remaining <= 60 and not self.one_minute_failsafe_sent:
                # Mark before starting the worker so repeated UI updates cannot spam Discord.
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
        self.update_warning_labels(now_mono)

        if remaining is not None and 0 < remaining <= ALARM_START_SECONDS:
            self.start_alarm()
        if remaining is not None and remaining <= 0:
            self.stop_alarm()
            self.play_failure_sound_once()

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
                [
                    "powershell.exe", "-NoLogo", "-NoProfile",
                    "-NonInteractive", "-ExecutionPolicy", "Bypass",
                    "-Command", powershell_script
                ],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                creationflags=creation_flags,
                close_fds=True
            )
        except Exception as exc:
            print("Speech announcement could not start:", exc)

    def announce_countdown_milestones(self, remaining):
        if self.deadline is None:
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
                        self.speak({
                            60: "One minute remaining.",
                            40: "Forty seconds remaining.",
                            20: "Twenty seconds remaining."
                        }[upcoming])
                        self.spoken_milestones.add(upcoming)
            self.last_speech_remaining = remaining
            if remaining <= 0 and 0 not in self.spoken_milestones:
                self.speak("Chain timeout expired.")
                self.spoken_milestones.add(0)
            return

        for milestone, phrase in (
            (60, "One minute remaining."),
            (40, "Forty seconds remaining."),
            (20, "Twenty seconds remaining.")
        ):
            if (
                milestone not in self.spoken_milestones
                and self.last_speech_remaining > milestone
                and remaining <= milestone
                and remaining > 0
            ):
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
        """Play slow heartbeat at 60-41s, normal at 40-21s, and fast at 20s to expiry."""
        while not self.alarm_stop_event.is_set():
            if self.deadline is None:
                return

            remaining = self.deadline - time.time()
            if remaining <= 0:
                return

            try:
                if winsound is not None:
                    if remaining <= 20:
                        # Fast final heartbeat: two quick tones.
                        winsound.Beep(FINAL_BEEP_FREQUENCY, FINAL_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.04):
                            return
                        winsound.Beep(FINAL_BEEP_FREQUENCY - 300, 120)
                        pause = FINAL_BEEP_PAUSE_MS / 1000.0
                    elif remaining <= 40:
                        # Normal heartbeat from 40 down to 21 seconds.
                        winsound.Beep(NORMAL_BEEP_FREQUENCY, NORMAL_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.10):
                            return
                        winsound.Beep(NORMAL_BEEP_FREQUENCY - 200, 180)
                        pause = NORMAL_BEEP_PAUSE_MS / 1000.0
                    elif remaining <= 60:
                        # Distinct slow heartbeat, active only from 60 through 40 seconds.
                        # Use two clearly audible tones with a longer pause than normal.
                        winsound.Beep(SLOW_BEEP_FREQUENCY, SLOW_BEEP_DURATION_MS)
                        if self.alarm_stop_event.wait(0.12):
                            return
                        winsound.Beep(SLOW_BEEP_FREQUENCY - 180, 180)
                        pause = SLOW_BEEP_PAUSE_MS / 1000.0
                    else:
                        # Do not play before the countdown enters the 60-second window.
                        pause = 0.05
                else:
                    pause = 0.2
            except Exception:
                pause = 0.2

            if self.alarm_stop_event.wait(pause):
                return

    def play_failure_sound_once(self):
        """Play a single continuous flatline tone when the countdown expires."""
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
        self.stop_alarm()
        self.root.destroy()



if __name__ == "__main__":
    root = tk.Tk()
    app = ChainTimerApp(root)
    root.mainloop()