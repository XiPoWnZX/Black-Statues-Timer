**# Black-Statues-Timer**

**ONLY FOR WINDOWS FOR NOW**

**STRICTLY RESTRICTED FOR *[Black Statues](https://www.torn.com/factions.php?step=profile&ID=9412)* faction from Torn City**

This is a private script for computer to always have the chain timer of Black Statues on your screen.

**Timer features**

Live faction chain countdown

Automatic API updates every 5 seconds

API key faction verification

Audio alerts during the final 60 seconds

Flashing countdown during the final minute

Compact countdown mode

Adjustable window opacity from 60% to 100%, defaulting to 85%

Always-on-top window

Draggable and lockable window

API connection and unchanged-timeout warnings

Automatic Google Sheets guard roster updates every 30 seconds

Clickable guard names that open their Torn profiles

Automatic 1-minute chain failsafe alert to a separate Discord channel, with a role mention, sent once per countdown

Automatic API polling on startup when a saved API key exists


***Black Statues Chain Timer — Installation Guide***

**1. Create your custom Torn API key**

The timer requires a custom API key to retrieve the Black Statues faction chain timer.

Create your Custom API key here: [Custom API](https://www.torn.com/preferences.php#tab=api?step=addNewKey&faction=chain,attacks&user=faction,attacks&title=Black%20Statues%20Chain%20Timer%20V2)

The timer verifies that your character belongs to BLACK STATUES (Faction ID: 9412). Keys belonging to other factions will be rejected.

Never share your API key with anyone.

You can run the [Black Statues Chain Timer.exe](https://github.com/XiPoWnZX/Black-Statues-Timer/blob/main/Black%20Statues%20Chain%20Timer.exe) and enter your API key from here.

From now you are ready to use the timer!

*If you want a manual installation continue and send me DM for non-redacted version*

**2. Install Python (if you don't already have it)**

The Black Statues Chain Timer requires Python to run.

Download Python here: https://www.python.org/downloads/windows/

Download the latest stable Python 3 release for Windows.

Run the installer.

IMPORTANT: Check the box that says “Add python.exe to PATH” before clicking Install.

Finish the installation.

Check that Python is installed

Press Windows + R.

Type cmd and press Enter.

In the command prompt, enter:

python --version

Press Enter. If Python is installed correctly, you should see a version number, such as Python 3.12.x.

If the command doesn't work, try:

py --version

If neither command works, reinstall Python and make sure you enable the option to add Python to PATH.


**3. Run the timer**

Download the Black Statues Chain Timer Python script. **[DOWNLOAD](https://github.com/XiPoWnZX/Black-Statues-Timer/blob/main/Black_Statues_Chain_Timer_Redacted.py)**

Save the file somewhere easy to find, such as your Desktop or Documents folder.

Double-click the .py file to launch it.

If double-clicking doesn't work:

Open the folder containing the script.

Click the address bar in File Explorer, type cmd, and press Enter.

Run the following command, replacing BlackStatuesChainTimer.py with your actual filename:

python BlackStatuesChainTimer.py

Click API Key in the window and enter your custom Torn API key.

Once the key is verified, click Start to enable automatic chain timer updates.


**Troubleshooting**

Python is not recognized: Reinstall Python and enable “Add python.exe to PATH,” or try the py command.

API key rejected: Make sure you enabled the required permissions and your character belongs to BLACK STATUES (Faction ID 9412).

The timer cannot connect: Check your internet connection and verify that your API key is valid.

Need help? Contact XiPoWnZX through in-game mail or Discord.

Any idea to add to this widget? Contact me.
