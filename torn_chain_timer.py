import time
import threading
import tkinter as tk
from tkinter import messagebox
import winsound
import requests
import json
from pathlib import Path

# ---------------- CONFIGURATION ----------------
FACTION_ID = 9412
POLL_SECONDS = 5
CONNECTION_STALE_SECONDS = 15
UNCHANGED_WARNING_SECONDS = 40

API_URL = f"https://api.torn.com/faction/{FACTION_ID}"

BG = "#151515"
RED = "#ff3030"
WHITE = "#ffffff"
GREY = "#bbbbbb"
YELLOW = "#ffd166"

# ---------------- LOCAL API KEY STORAGE ----------------
CONFIG_FILE = (
    Path.home()
    / "AppData"
    / "Roaming"
    / "TornChainTimer"
    / "config.json"
)


def load_saved_api_key():
    """Load the saved API key from this computer."""
    try:
        data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        return data.get("api_key", "")
    except (OSError, ValueError, TypeError):
        return ""


def save_api_key(key):
    """Save the API key locally."""
    CONFIG_FILE.parent.mkdir(parents=True, exist_ok=True)
    CONFIG_FILE.write_text(
        json.dumps({"api_key": key}),
        encoding="utf-8"
    )


# ---------------- MAIN WINDOW ----------------
root = tk.Tk()
root.title("Black Statues Chain Timer")
root.configure(bg=BG)
root.attributes("-topmost", True)
root.resizable(False, False)

WIDTH, HEIGHT = 340, 225
screen_w = root.winfo_screenwidth()
root.geometry(f"{WIDTH}x{HEIGHT}+{screen_w-WIDTH-25}+40")

# ---------------- APP STATE ----------------
api_key = ""
running = False
request_in_progress = False

deadline = None
last_success = None
last_value_change = None
last_api_timeout = None
last_poll_started = 0.0

sound_played = False
flash_on = True
last_error = ""

# ---------------- COMPACT WINDOW STATE ----------------
compact = None
compact_timer_label = None
compact_status_label = None


# ---------------- MAIN WINDOW WIDGETS ----------------
title_label = tk.Label(
    root,
    text="BLACK STATUES CHAIN",
    bg=BG,
    fg=WHITE,
    font=("Segoe UI", 10, "bold")
)
title_label.pack(pady=(8, 0))

timer_label = tk.Label(
    root,
    text="--:--",
    bg=BG,
    fg=RED,
    font=("Consolas", 36, "bold")
)
timer_label.pack()

status_label = tk.Label(
    root,
    text="Enter your API key and press Start",
    bg=BG,
    fg=GREY,
    font=("Segoe UI", 8),
    wraplength=320
)
status_label.pack(padx=8)

key_entry = tk.Entry(
    root,
    width=32,
    show="*",
    bg="#292929",
    fg=WHITE,
    insertbackground=WHITE
)
key_entry.pack(pady=(6, 5))

# Load the saved key AFTER creating the entry.
saved_key = load_saved_api_key()
if saved_key:
    key_entry.insert(0, saved_key)


# ---------------- STATUS ----------------
def set_status(text, color=GREY):
    status_label.config(text=text, fg=color)

    if compact_status_label is not None:
        try:
            compact_status_label.config(text=text, fg=color)
        except tk.TclError:
            pass


# ---------------- ALERTS AND FORMATTING ----------------
def play_alert():
    try:
        winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
    except Exception:
        pass


def fmt_time(seconds):
    seconds = max(0, int(seconds))
    minutes, seconds = divmod(seconds, 60)
    return f"{minutes:02d}:{seconds:02d}"


# ---------------- WINDOW MANAGEMENT ----------------
def show_compact():
    """Hide settings and show the small floating counter."""
    global compact, compact_timer_label, compact_status_label

    if compact is not None and compact.winfo_exists():
        compact.deiconify()
        compact.lift()
        compact.attributes("-topmost", True)
        root.withdraw()
        return

    compact = tk.Toplevel(root)
    compact.title("Black Statues Chain")
    compact.configure(bg=BG)
    compact.attributes("-topmost", True)
    compact.resizable(False, False)
    compact.overrideredirect(True)

    compact_width = 225
    compact_height = 100
    x = compact.winfo_screenwidth() - compact_width - 15
    compact.geometry(f"{compact_width}x{compact_height}+{x}+35")

    header = tk.Frame(compact, bg=BG)
    header.pack(fill="x", padx=7, pady=(4, 0))

    tk.Label(
        header,
        text="BLACK STATUES CHAIN",
        bg=BG,
        fg=WHITE,
        font=("Segoe UI", 8, "bold")
    ).pack(side="left")

    tk.Button(
        header,
        text="Settings",
        command=show_settings,
        bg="#333333",
        fg=WHITE,
        relief="flat",
        font=("Segoe UI", 7),
        padx=5,
        pady=1
    ).pack(side="right", padx=(3, 0))

    tk.Button(
        header,
        text="X",
        command=close_app,
        bg="#552222",
        fg=WHITE,
        relief="flat",
        font=("Segoe UI", 8, "bold"),
        padx=5,
        pady=1
    ).pack(side="right")

    compact_timer_label = tk.Label(
        compact,
        text="--:--",
        bg=BG,
        fg=RED,
        font=("Consolas", 30, "bold")
    )
    compact_timer_label.pack(pady=(0, 0))

    compact_status_label = tk.Label(
        compact,
        text="CONNECTING...",
        bg=BG,
        fg=GREY,
        font=("Segoe UI", 7),
        wraplength=215
    )
    compact_status_label.pack(pady=(0, 3))

    # Allow dragging the small counter around the screen.
    def drag_start(event):
        compact._drag_x = event.x_root - compact.winfo_x()
        compact._drag_y = event.y_root - compact.winfo_y()

    def drag_move(event):
        x_new = event.x_root - compact._drag_x
        y_new = event.y_root - compact._drag_y
        compact.geometry(f"+{x_new}+{y_new}")

    for widget in (
        compact,
        header,
        compact_timer_label,
        compact_status_label
    ):
        widget.bind("<Button-1>", drag_start)
        widget.bind("<B1-Motion>", drag_move)

    root.withdraw()


def show_settings():
    """Show the settings window without stopping the timer."""
    root.deiconify()
    root.lift()
    root.attributes("-topmost", True)

    if compact is not None and compact.winfo_exists():
        compact.withdraw()


def return_to_counter():
    """Return to the compact counter without stopping the timer."""
    if not running:
        messagebox.showinfo(
            "Timer arrêté",
            "Clique sur Start pour lancer le compteur."
        )
        return

    show_compact()


def close_app():
    """Stop the timer and close the application."""
    global running, api_key

    running = False
    api_key = ""
    root.destroy()


# ---------------- API REQUEST ----------------
def fetch_chain():
    global request_in_progress, last_poll_started

    if not running or request_in_progress:
        return

    request_in_progress = True
    last_poll_started = time.monotonic()
    key = api_key

    def worker():
        result = None
        error = None

        try:
            response = requests.get(
                API_URL,
                params={
                    "selections": "chain",
                    "key": key,
                    "timestamp": int(time.time())
                },
                timeout=8
            )
            response.raise_for_status()
            data = response.json()

            if "error" in data:
                api_error = data["error"]
                error = "Torn API error: " + str(
                    api_error.get("error", api_error)
                )
            else:
                chain = data.get("chain")

                if not isinstance(chain, dict):
                    error = "No chain data in response"
                elif "timeout" not in chain:
                    error = "Chain timeout field is missing"
                else:
                    result = float(chain["timeout"])

                    if result < 0:
                        error = "Invalid negative timeout"
                        result = None

        except requests.Timeout:
            error = "Request timed out"
        except requests.RequestException as exc:
            error = f"Network error: {exc}"
        except (ValueError, TypeError) as exc:
            error = f"Unexpected API response: {exc}"
        except Exception as exc:
            error = f"Unexpected error: {exc}"

        def apply_result():
            global request_in_progress, last_success
            global last_value_change, last_api_timeout
            global deadline, sound_played, last_error

            request_in_progress = False

            if not running:
                return

            now = time.monotonic()

            if error is not None:
                last_error = error
                update_display()
                return

            last_success = now
            last_error = ""

            if result is None:
                update_display()
                return

            if deadline is None:
                deadline = now + result
                last_api_timeout = result
                last_value_change = now
                sound_played = False

            else:
                predicted = max(0.0, deadline - now)

                # Do not restart the timer from unchanged API data.
                if (
                    last_api_timeout is None
                    or abs(result - last_api_timeout) >= 1
                ):
                    last_value_change = now

                    if result > predicted + 4:
                        deadline = now + result
                        sound_played = False
                    elif result < predicted - 4:
                        deadline = now + result

                    last_api_timeout = result

            update_display()

        try:
            root.after(0, apply_result)
        except tk.TclError:
            pass

    threading.Thread(target=worker, daemon=True).start()


# ---------------- DISPLAY AND TIMER ----------------
def update_display():
    global flash_on, sound_played

    if not running:
        return

    now = time.monotonic()

    if deadline is None:
        display_text = "--:--"
        timer_color = RED

    else:
        remaining = max(0, deadline - now)
        display_text = fmt_time(remaining)

        # Play the alert once when 30 seconds remain.
        if remaining <= 30 and not sound_played:
            play_alert()
            sound_played = True

        # Flash the timer at 60 seconds or less.
        if remaining <= 60:
            flash_on = not flash_on
            timer_color = RED if flash_on else BG
        else:
            timer_color = RED

    timer_label.config(text=display_text, fg=timer_color)

    if compact_timer_label is not None:
        try:
            compact_timer_label.config(
                text=display_text,
                fg=timer_color
            )
        except tk.TclError:
            pass

    # Connection and data warnings.
    if last_success is None:
        set_status(
            "CONNECTING • waiting for first API response",
            YELLOW
        )

    elif now - last_success > CONNECTION_STALE_SECONDS:
        set_status("STALE DATA • API connection failed", RED)

    elif (
        last_value_change is not None
        and now - last_value_change > UNCHANGED_WARNING_SECONDS
        and deadline is not None
        and deadline > now
    ):
        set_status(
            "CHECK DATA • API timeout hasn't changed",
            YELLOW
        )

    elif last_error:
        set_status("API WARNING • " + last_error[:45], YELLOW)

    else:
        age = int(now - last_success)
        set_status(f"CONNECTED • last response {age}s ago", GREY)


def tick():
    if not running:
        return

    update_display()

    now = time.monotonic()

    if (
        not request_in_progress
        and now - last_poll_started >= POLL_SECONDS
    ):
        fetch_chain()

    root.after(250, tick)


# ---------------- BUTTON ACTIONS ----------------
def start_timer():
    global api_key, running, deadline
    global last_success, last_value_change, last_api_timeout
    global sound_played, last_poll_started, last_error

    key = key_entry.get().strip()

    if not key:
        messagebox.showwarning(
            "API key required",
            "Enter your Torn API key first."
        )
        return

    # Save the API key locally.
    try:
        save_api_key(key)
    except OSError as exc:
        messagebox.showwarning(
            "Sauvegarde impossible",
            f"La clé ne pourra pas être sauvegardée : {exc}"
        )

    api_key = key
    running = True
    deadline = None
    last_success = None
    last_value_change = None
    last_api_timeout = None
    sound_played = False
    last_poll_started = 0.0
    last_error = ""

    key_entry.config(state="disabled")
    start_button.config(state="disabled")

    set_status("Connecting to Torn...", YELLOW)

    # Immediately switch to the small counter.
    show_compact()

    fetch_chain()
    tick()


def stop_timer():
    global api_key, running, deadline

    running = False
    api_key = ""
    deadline = None

    key_entry.config(state="normal")
    start_button.config(state="normal")

    timer_label.config(text="--:--", fg=RED)

    if compact_timer_label is not None:
        try:
            compact_timer_label.config(text="--:--", fg=RED)
        except tk.TclError:
            pass

    set_status("Stopped")

    if compact is not None and compact.winfo_exists():
        compact.withdraw()

    root.deiconify()
    root.lift()


# ---------------- BUTTONS ----------------
return_button = tk.Button(
    root,
    text="Countdown",
    command=return_to_counter,
    bg="#333333",
    fg=WHITE,
    activebackground="#555555"
)
return_button.pack(pady=(5, 2))

button_frame = tk.Frame(root, bg=BG)
button_frame.pack(pady=(2, 7))

start_button = tk.Button(
    button_frame,
    text="Start",
    command=start_timer,
    bg="#333333",
    fg=WHITE,
    activebackground="#555555",
    width=10
)
start_button.pack(side="left", padx=5)

stop_button = tk.Button(
    button_frame,
    text="Stop",
    command=stop_timer,
    bg="#333333",
    fg=WHITE,
    activebackground="#555555",
    width=10
)
stop_button.pack(side="left", padx=5)

root.protocol("WM_DELETE_WINDOW", close_app)
root.mainloop()
