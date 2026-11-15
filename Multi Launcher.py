"""
Multi-Launcher - Roblox multi-account launcher (formerly Crimson Launcher)
- Save accounts (passwords/cookies encrypted with Windows DPAPI)
- Log in through Microsoft Edge (one window for all accounts)
- Launch many accounts at once, retrying until every client is up
- Join a friend or any user, friends list with avatars
- Automatic restart of crashed / frozen / disconnected clients
- Change display names, bio, follow users
- Lean clients: lower priority, trimmed memory, frame-rate cap
- Clean black-and-white GUI with an activity log
"""
import base64
import collections
import csv
import ctypes
import json
import math
import os
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.parse
import uuid
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from concurrent.futures import ThreadPoolExecutor
from ctypes import wintypes
from tkinter import messagebox, simpledialog, ttk

import requests


APP_NAME = "Multi-Launcher"
APP_VERSION = "3.8"
FROZEN = bool(getattr(sys, "frozen", False))  # True when running as the packaged .exe
APP_DIR = os.path.dirname(os.path.abspath(sys.executable if FROZEN else __file__))
PROC_NAME = "RobloxPlayerBeta.exe"
MAX_RETRIES = 15
RETRY_WINDOW_SECONDS = 5 * 60
WAIT_PER_TRY = 35
LAUNCH_PAUSE = 3
STABLE_SECONDS = 12  # a client must stay alive this long to count as started
PURCHASE_VERIFY_ATTEMPTS = 3
AVATAR_APPLY_ATTEMPTS = 3
NO_WINDOW = 0x08000000
DETACHED_PROCESS = 0x00000008
CREATE_NEW_PROCESS_GROUP = 0x00000200


# --------------------------------------------------------------------------
# Persistent user data (Documents\Roblox Multi Launcher)
# --------------------------------------------------------------------------
def _writable(d):
    try:
        os.makedirs(d, exist_ok=True)
        t = os.path.join(d, ".write_test")
        with open(t, "w", encoding="utf-8") as f:
            f.write("x")
        os.remove(t)
        return True
    except Exception:
        return False


def _documents_dir():
    try:
        buf = ctypes.create_unicode_buffer(260)
        if ctypes.windll.shell32.SHGetFolderPathW(0, 5, 0, 0, buf) == 0 and buf.value:
            return buf.value
    except Exception:
        pass
    return os.path.join(os.path.expanduser("~"), "Documents")


_DOCS = _documents_dir()
PREFERRED_DATA_DIR = os.path.join(_DOCS, "Multi-Launcher")
if _writable(PREFERRED_DATA_DIR):
    DATA_DIR = PREFERRED_DATA_DIR
elif _writable(APP_DIR):
    DATA_DIR = APP_DIR
else:
    DATA_DIR = os.path.join(os.environ.get("APPDATA", APP_DIR), "Multi-Launcher")
    os.makedirs(DATA_DIR, exist_ok=True)

DATA_FILE = os.path.join(DATA_DIR, "accounts.json")
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")
FRIENDS_FILE = os.path.join(DATA_DIR, "friends.json")
EDGE_PROFILE = os.path.join(DATA_DIR, "edge_profile")
FLEET_DIR = os.path.join(DATA_DIR, "edge_fleet")  # one separate Edge profile per account
EXTENSION_DIR = os.path.join(DATA_DIR, "crimson_edge_extension")
MIGRATION_MESSAGES = []


_UI_LIB_JS = r'''(() => {
  if (window.__crimsonUI) return;
  // Areas that must never be clicked: site navigation, footer and social links (Facebook, Twitter ...).
  const SKIP = 'footer, nav, #footer-container, .footer, .footer-container, .navbar, #header, .rbx-header, '
    + '.rbx-navbar, [role="navigation"], [role="contentinfo"], [class*="social" i], '
    + '[aria-label*="facebook" i], [aria-label*="twitter" i], [aria-label*="youtube" i], [aria-label*="twitch" i]';
  const CLICKABLE = 'button, [role="button"], [role="menuitem"], a[href], input[type="button"], input[type="submit"]';
  const DIALOG = '[role="dialog"], [role="alertdialog"], .modal-dialog, .modal.in, .modal.show, .modal-content';
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const lower = (s) => (s || '').toString().toLowerCase();
  const visible = (e) => {
    if (!e || !e.getBoundingClientRect) return false;
    const r = e.getBoundingClientRect();
    if (r.width <= 0 || r.height <= 0) return false;
    const st = getComputedStyle(e);
    return st.visibility !== 'hidden' && st.display !== 'none' && st.opacity !== '0';
  };
  const hostOk = (href) => {
    try {
      const u = new URL(href, location.href);
      return u.hostname === 'roblox.com' || u.hostname.endsWith('.roblox.com');
    } catch (e) { return false; }
  };
  // A link is only safe when it stays on roblox.com and does not open a new tab.
  const safe = (e) => {
    const a = e.closest('a[href]');
    if (!a) return true;
    const href = a.getAttribute('href') || '';
    if (a.getAttribute('target') === '_blank') return false;
    if (/^(mailto|tel|javascript):/i.test(href)) return false;
    return hostOk(href);
  };
  const textOf = (e) => ((e.innerText || e.value || e.getAttribute('aria-label') || '') + '').trim();
  const main = () => {
    for (const sel of ['main', '[role="main"]', '#container-main', '#content', '.content']) {
      const m = document.querySelector(sel);
      if (m && visible(m)) return m;
    }
    return document.body;
  };
  const dialog = () => [...document.querySelectorAll(DIALOG)].filter(visible).pop() || null;
  const find = (re, root, opts = {}) => {
    const scope = root || document;
    const list = [...scope.querySelectorAll(CLICKABLE)].filter((e) => visible(e) && !e.disabled
      && e.getAttribute('aria-disabled') !== 'true' && !e.closest(SKIP) && safe(e));
    const hit = list.filter((e) => re.test(textOf(e)) && !(opts.not && opts.not.test(textOf(e))));
    hit.sort((a, b) => (a.tagName === 'A') - (b.tagName === 'A')); // buttons before links
    return hit[0] || null;
  };
  const click = (e) => {
    e.scrollIntoView({ block: 'center' });
    for (const t of ['mousedown', 'mouseup']) {
      e.dispatchEvent(new MouseEvent(t, { bubbles: true, cancelable: true, view: window }));
    }
    e.click();
  };
  const waitFor = async (fn, ms = 8000, step = 120) => {
    const end = Date.now() + ms;
    for (;;) {
      let v = null;
      try { v = fn(); } catch (e) { v = null; }
      if (v) return v;
      if (Date.now() > end) return null;
      await sleep(step);
    }
  };
  const setValue = (el, text) => {
    el.focus();
    if (el.isContentEditable) {
      el.textContent = text;
    } else {
      const proto = el.tagName === 'TEXTAREA' ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
      Object.getOwnPropertyDescriptor(proto, 'value').set.call(el, text);
    }
    el.dispatchEvent(new Event('input', { bubbles: true }));
    el.dispatchEvent(new Event('change', { bubbles: true }));
  };
  const info = (e) => lower([e.getAttribute('aria-label'), e.getAttribute('placeholder'), e.name, e.id,
    (e.labels && e.labels[0] && e.labels[0].innerText) || '', e.closest('label') ? e.closest('label').innerText : ''].join(' '));
  const sameRow = (a, b, tol) => {
    const ra = a.getBoundingClientRect(), rb = b.getBoundingClientRect();
    return Math.abs((ra.top + ra.height / 2) - (rb.top + rb.height / 2)) <= tol;
  };
  const LIMIT_RE = /once every|7 days|cooldown|can only be changed|cannot change|can't change/i;
  const RATE_RE = /too many|try again later|throttl|rate limit|zu viele/i;
  // After pressing Save: read a visible error message (dialog / alert) so the launcher can stop on a limit.
  const afterSave = async () => {
    await sleep(900);
    const roots = [dialog(), main()].filter(Boolean);
    for (const r of roots) {
      const els = r.querySelectorAll('[role="alert"], .alert-warning, .alert-error, .alert-danger, .text-error, .form-control-error, .error-message');
      for (const e of els) {
        const t = ((e.innerText || '') + '').trim();
        if (visible(e) && !e.closest(SKIP) && t && t.length < 300) {
          return { ok: false, code: LIMIT_RE.test(t) ? 'limit' : (RATE_RE.test(t) ? 'ratelimit' : 'rejected'), message: t.slice(0, 160) };
        }
      }
    }
    return null;
  };
  const confirmDialog = async () => {
    await sleep(500);
    const d = dialog();
    if (!d) return false;
    const b = find(/^(confirm|yes|ok|continue|change|save)$/i, d);
    if (b) { click(b); return true; }
    return false;
  };

  const aboutField = () => {
    const d = dialog();
    const root = d || main();
    const fields = [...root.querySelectorAll('textarea, [contenteditable="true"], [contenteditable=""], [role="textbox"]')]
      .filter((e) => visible(e) && !e.closest(SKIP));
    if (!fields.length) return null;
    const labelled = fields.find((e) => /about|bio|description|describe|beschreibung|über mich/.test(info(e)));
    if (labelled) return labelled;
    if (!d) return null; // outside a dialog the field must be clearly labelled
    fields.sort((a, b) => b.getBoundingClientRect().height - a.getBoundingClientRect().height);
    return fields[0];
  };

  const actions = {
    // Own profile page: Edit Profile -> About -> text -> Save
    async bio(args) {
      let area = aboutField();
      if (!area) {
        const edit = await waitFor(() => find(/^edit profile$/i, main()), 9000);
        if (!edit) return { ok: false, code: 'noedit' };
        click(edit);
        area = await waitFor(aboutField, 8000);
      }
      if (!area) return { ok: false, code: 'noinput' };
      setValue(area, args.text || '');
      const scope = area.closest(DIALOG) || dialog() || main();
      const save = await waitFor(() => find(/^(save|update|done|confirm|apply)$/i, scope), 4000);
      if (!save) return { ok: false, code: 'nosave' };
      click(save);
      await confirmDialog();
      const bad = await afterSave();
      if (bad) return bad;
      return { ok: true, code: 'saved' };
    },

    // Settings > Account Info: pencil next to "Display Name" -> new name -> Save
    async displayName(args) {
      const label = await waitFor(() => [...main().querySelectorAll('label, span, div, p, h3, h4, h5, th, td, dt')]
        .find((e) => visible(e) && !e.closest(SKIP) && /^display name\b/i.test((e.innerText || '').trim())
          && (e.innerText || '').trim().length < 40), 9000);
      if (!label) return { ok: false, code: 'nolabel' };
      let edit = null;
      let node = label;
      for (let i = 0; i < 5 && node && node !== document.body && !edit; i++, node = node.parentElement) {
        edit = [...node.querySelectorAll('button, [role="button"], a:not([href]), a[href^="#"], [class*="edit" i], [class*="pencil" i]')]
          .find((e) => e !== label && visible(e) && !e.closest(SKIP) && safe(e) && sameRow(e, label, 40)) || null;
      }
      if (!edit) return { ok: false, code: 'noedit' };
      click(edit);
      const input = await waitFor(() => {
        const d = dialog();
        const pool = d ? [...d.querySelectorAll('input')]
          : [...main().querySelectorAll('input')].filter((i) => sameRow(i, label, 70));
        return pool.find((i) => visible(i) && ['text', 'search', ''].includes((i.getAttribute('type') || '').toLowerCase())) || null;
      }, 8000);
      if (!input) return { ok: false, code: 'noinput' };
      setValue(input, args.name || '');
      const scope = input.closest(DIALOG) || dialog() || main();
      const save = await waitFor(() => find(/^(save|update|change|confirm|submit|done)$/i, scope), 4000);
      if (!save) return { ok: false, code: 'nosave' };
      click(save);
      await confirmDialog();
      const bad = await afterSave();
      if (bad) return bad;
      return { ok: true, code: 'saved' };
    },

    // Another user's profile: Follow button (or inside the profile's own "..." menu)
    async follow() {
      const root = main();
      if (find(/^(unfollow|following)$/i, root)) return { ok: true, code: 'already' };
      let btn = await waitFor(() => find(/^follow$/i, root), 5000);
      if (!btn) {
        const header = document.querySelector('.profile-header, [class*="profile-header" i], [class*="ProfileHeader"], [data-testid*="profile" i]') || root;
        const more = [...header.querySelectorAll('button, [role="button"]')].find((b) => visible(b)
          && !b.closest(SKIP) && safe(b) && /more|option|menu|dots|ellipsis|kebab|overflow/.test(info(b) + ' ' + lower(b.className)));
        if (more) {
          click(more);
          btn = await waitFor(() => find(/^follow$/i, document), 3000);
        }
      }
      if (!btn) return { ok: false, code: 'nofollow' };
      click(btn);
      await sleep(500);
      return { ok: true, code: 'followed' };
    },

    // Item page: Get / Buy, then the confirmation (Get Now / Buy Now)
    async buy() {
      const root = main();
      const btn = await waitFor(() => find(/^(get|buy)\b/i, root, { not: /robux|\bnow\b/i }), 9000);
      if (!btn) return { ok: false, code: 'nobutton' };
      click(btn);
      const confirm = await waitFor(() => {
        const d = dialog();
        return d ? find(/^(buy now|get now|confirm|purchase|buy|get)\b/i, d) : null;
      }, 4000);
      if (confirm) click(confirm);
      await sleep(400);
      return { ok: true, code: confirm ? 'confirmed' : 'clicked' };
    },

    // Click the confirmation of an open dialog (used after a verification)
    async confirm() {
      return { ok: await confirmDialog(), code: 'confirm' };
    },
  };

  window.__crimsonUI = {
    version: 1,
    where: () => location.href,
    run: async (action, args) => {
      try {
        const f = actions[action];
        if (!f) return { ok: false, code: 'unknown' };
        return await f(args || {});
      } catch (e) {
        return { ok: false, code: 'exception', error: String(e) };
      }
    },
  };
})();
'''


def _ensure_edge_extension():
    """Install Crimson's local, unpacked Edge bridge for the dedicated profiles.

    It is never added to the user's everyday Edge profile.  The bridge only
    handles the approved Roblox Marketplace request issued by this launcher.
    """
    manifest = {
        "manifest_version": 3,
        "name": "Crimson Roblox Bridge",
        "version": "1.1.0",
        "description": "Local bridge used by Multi-Launcher for approved Roblox actions.",
        "content_scripts": [
            {"matches": ["https://www.roblox.com/*"], "js": ["bridge.js"], "run_at": "document_start"},
            # Safe click library (never touches navigation, footer or social links): loaded into the page itself.
            {"matches": ["https://www.roblox.com/*"], "js": ["ui_lib.js"], "run_at": "document_idle",
             "world": "MAIN"},
        ],
        "web_accessible_resources": [{"resources": ["page_bridge.js"], "matches": ["https://www.roblox.com/*"]}],
    }
    bridge = """(() => {\n  if (window.__crimsonBridgeInstalled) return;\n  window.__crimsonBridgeInstalled = true;\n  const add = () => {\n    if (document.getElementById('crimson-page-bridge')) return;\n    const s = document.createElement('script');\n    s.id = 'crimson-page-bridge';\n    s.src = chrome.runtime.getURL('page_bridge.js');\n    (document.documentElement || document.head).appendChild(s);\n  };\n  add();\n})();\n"""
    page_bridge = """(() => {\n  if (window.__crimsonPageBridgeInstalled) return;\n  window.__crimsonPageBridgeInstalled = true;\n  window.addEventListener('message', async (event) => {\n    const d = event.data || {};\n    if (event.source !== window || d.source !== 'CrimsonLauncher' || d.type !== 'purchase') return;\n    const done = (payload) => window.postMessage({source: 'CrimsonEdgeBridge', requestId: d.requestId, ...payload}, location.origin);\n    const productId = Number(d.productId), price = Number(d.price), sellerId = Number(d.sellerId);\n    if (!Number.isFinite(productId) || !Number.isFinite(price) || !Number.isFinite(sellerId) || price < 0) {\n      done({status: 0, error: 'invalid purchase request'}); return;\n    }\n    const post = async (token) => fetch('https://economy.roblox.com/v1/purchases/products/' + productId, {\n      method: 'POST', credentials: 'include',\n      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': token || ''},\n      body: JSON.stringify({expectedCurrency: 1, expectedPrice: price, expectedSellerId: sellerId})\n    });\n    try {\n      let r = await post('');\n      if (r.status === 403) { const token = r.headers.get('x-csrf-token'); if (token) r = await post(token); }\n      let body = null; try { body = await r.json(); } catch (_) {}\n      done({status: r.status, body, challenge: r.headers.get('rblx-challenge-id') || null});\n    } catch (err) { done({status: 0, error: String(err)}); }\n  });\n})();\n"""
    try:
        os.makedirs(EXTENSION_DIR, exist_ok=True)
        with open(os.path.join(EXTENSION_DIR, "manifest.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f, indent=2)
        with open(os.path.join(EXTENSION_DIR, "bridge.js"), "w", encoding="utf-8") as f:
            f.write(bridge)
        with open(os.path.join(EXTENSION_DIR, "page_bridge.js"), "w", encoding="utf-8") as f:
            f.write(page_bridge)
        with open(os.path.join(EXTENSION_DIR, "ui_lib.js"), "w", encoding="utf-8") as f:
            f.write(_UI_LIB_JS)
        return True
    except OSError as exc:
        MIGRATION_MESSAGES.append(f"Could not prepare Crimson Edge extension: {exc}")
        return False


def _migrate_and_install():
    """Keep existing account data and Edge profile in the user's established folder."""
    try:
        legacy_dirs = [
            os.path.join(_DOCS, "Roblox Multi Launcher"),
            os.path.join(_DOCS, "RobloxMultiLauncher"),
            os.path.join(_DOCS, "CrimsonLauncher"),
            APP_DIR,
            os.path.join(os.environ.get("APPDATA", ""), "RobloxMultiLauncher"),
            os.path.join(os.environ.get("APPDATA", ""), "CrimsonLauncher"),
        ]
        # Do not copy a file onto itself. Keep a populated destination; if a
        # previous first-run created an empty/broken accounts file, recover the
        # first usable account list from the older data folder instead.
        accounts_destination = os.path.join(DATA_DIR, "accounts.json")
        destination_has_accounts = False
        if os.path.isfile(accounts_destination):
            try:
                with open(accounts_destination, "r", encoding="utf-8") as f:
                    existing_accounts = json.load(f)
                destination_has_accounts = isinstance(existing_accounts, list) and bool(existing_accounts)
            except (OSError, ValueError, TypeError):
                destination_has_accounts = False
        if not destination_has_accounts:
            for folder in legacy_dirs:
                source = os.path.join(folder, "accounts.json")
                if not os.path.isfile(source) or os.path.abspath(source) == os.path.abspath(accounts_destination):
                    continue
                try:
                    with open(source, "r", encoding="utf-8") as f:
                        candidate_accounts = json.load(f)
                    if not isinstance(candidate_accounts, list) or not candidate_accounts:
                        continue
                    if os.path.isfile(accounts_destination):
                        backup = accounts_destination + ".backup"
                        if not os.path.exists(backup):
                            shutil.copy2(accounts_destination, backup)
                    shutil.copy2(source, accounts_destination)
                    MIGRATION_MESSAGES.append(f"Imported saved accounts from {folder}.")
                    destination_has_accounts = True
                    break
                except (OSError, ValueError, TypeError):
                    continue

        settings_destination = os.path.join(DATA_DIR, "settings.json")
        settings_valid = False
        if os.path.isfile(settings_destination):
            try:
                with open(settings_destination, "r", encoding="utf-8") as f:
                    settings_valid = isinstance(json.load(f), dict)
            except (OSError, ValueError, TypeError):
                settings_valid = False
        if not settings_valid:
            for folder in legacy_dirs:
                source = os.path.join(folder, "settings.json")
                if not os.path.isfile(source) or os.path.abspath(source) == os.path.abspath(settings_destination):
                    continue
                try:
                    with open(source, "r", encoding="utf-8") as f:
                        if not isinstance(json.load(f), dict):
                            continue
                    if os.path.isfile(settings_destination):
                        backup = settings_destination + ".backup"
                        if not os.path.exists(backup):
                            shutil.copy2(settings_destination, backup)
                    shutil.copy2(source, settings_destination)
                    MIGRATION_MESSAGES.append(f"Imported settings from {folder}.")
                    break
                except (OSError, ValueError, TypeError):
                    continue

        if not os.path.isdir(EDGE_PROFILE):
            for folder in legacy_dirs:
                source_profile = os.path.join(folder, "edge_profile")
                if os.path.isdir(source_profile) and os.path.abspath(source_profile) != os.path.abspath(EDGE_PROFILE):
                    shutil.copytree(source_profile, EDGE_PROFILE, dirs_exist_ok=True)
                    MIGRATION_MESSAGES.append(f"Imported Edge sign-in profile from {folder}.")
                    break

        for item in ("custom_flags.json", "friends.json", "edge_fleet"):
            for folder in legacy_dirs:
                source = os.path.join(folder, item)
                target = os.path.join(DATA_DIR, item)
                if os.path.exists(target) or not os.path.exists(source) or os.path.abspath(source) == os.path.abspath(target):
                    continue
                try:
                    if os.path.isdir(source):
                        shutil.copytree(source, target, dirs_exist_ok=True)
                    else:
                        shutil.copy2(source, target)
                except OSError:
                    continue
                break
    except Exception as exc:
        MIGRATION_MESSAGES.append(f"Data migration warning: {exc}")


def _ensure_python_packages():
    """Install what Edge control needs (websocket-client) automatically instead of asking the user."""
    if FROZEN:
        return  # the .exe already contains it
    try:
        import websocket  # noqa: F401
        return
    except ImportError:
        pass
    MIGRATION_MESSAGES.append("Installing the missing Python package websocket-client ...")
    try:
        subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "websocket-client"],
                       capture_output=True, text=True, timeout=240,
                       creationflags=NO_WINDOW if os.name == "nt" else 0)
        import importlib
        importlib.invalidate_caches()
        import websocket  # noqa: F401
        MIGRATION_MESSAGES.append("Installed websocket-client automatically.")
    except Exception:
        MIGRATION_MESSAGES.append(
            "Could not install websocket-client automatically. Run: python -m pip install websocket-client")


_migrate_and_install()
_ensure_python_packages()
if _ensure_edge_extension():
    MIGRATION_MESSAGES.append("Edge add-on 'Crimson Roblox Bridge' is prepared and will load automatically.")


def minimize_console_window():
    """Minimize an attached Windows console (for example, PowerShell) without hiding it."""
    if os.name != "nt":
        return
    try:
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 6)  # SW_MINIMIZE
    except Exception:
        pass


# --------------------------------------------------------------------------
# Windows DPAPI
# --------------------------------------------------------------------------
class DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]


def _blob(data: bytes):
    buf = ctypes.create_string_buffer(data, len(data))
    return DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char))), buf


def encrypt(text: str) -> str:
    if not text:
        return ""
    blob_in, _keep = _blob(text.encode("utf-8"))
    blob_out = DATA_BLOB()
    if not ctypes.windll.crypt32.CryptProtectData(
        ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)
    ):
        raise RuntimeError("Encryption failed")
    raw = ctypes.string_at(blob_out.pbData, blob_out.cbData)
    ctypes.windll.kernel32.LocalFree(blob_out.pbData)
    return base64.b64encode(raw).decode()


def decrypt(token: str) -> str:
    if not token:
        return ""
    try:
        raw = base64.b64decode(token)
        blob_in, _keep = _blob(raw)
        blob_out = DATA_BLOB()
        if not ctypes.windll.crypt32.CryptUnprotectData(
            ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)
        ):
            return ""
        out = ctypes.string_at(blob_out.pbData, blob_out.cbData)
        ctypes.windll.kernel32.LocalFree(blob_out.pbData)
        return out.decode("utf-8")
    except Exception:
        return ""


# --------------------------------------------------------------------------
# Processes
# --------------------------------------------------------------------------
_mutex_handle = None


def hold_singleton_mutex():
    """Lets several Roblox clients run side by side while this program is open."""
    global _mutex_handle
    try:
        _mutex_handle = ctypes.windll.kernel32.CreateMutexW(None, True, "ROBLOX_singletonMutex")
    except Exception:
        _mutex_handle = None


def parse_process_snapshot(output):
    """Parse verbose tasklist CSV into running and not-responding PID sets."""
    pids, hung = set(), set()
    for row in csv.reader(output.splitlines()):
        if len(row) < 2 or row[0].lower() != PROC_NAME.lower() or not row[1].isdigit():
            continue
        pid = int(row[1])
        pids.add(pid)
        # In verbose tasklist output, Status is column 6 (index 5).
        if len(row) > 5:
            status = row[5].lower()
            if any(marker in status for marker in ("not responding", "keine rückmeldung", "reagiert nicht")):
                hung.add(pid)
    return pids, hung


def process_snapshot(verbose=True):
    """Return process sets, or (None, None) when Windows cannot answer the query.
    verbose=False skips the slow window-status query (enough to detect new clients)."""
    if not verbose:
        fast = native_roblox_pids()
        if fast is not None:
            return fast, set()
    try:
        result = subprocess.run(
            ["tasklist", "/FO", "CSV", "/NH"] + (["/V"] if verbose else [])
            + ["/FI", f"IMAGENAME eq {PROC_NAME}"],
            capture_output=True, text=True, creationflags=NO_WINDOW, timeout=8
        )
        if result.returncode != 0:
            return None, None
        return parse_process_snapshot(result.stdout or "")
    except Exception:
        return None, None


def roblox_pids():
    pids, _ = process_snapshot()
    return pids if pids is not None else set()


def hung_pids():
    _, hung = process_snapshot()
    return hung if hung is not None else set()


def kill_pid(pid):
    try:
        if int(pid) > 0:
            subprocess.run(
                ["taskkill", "/PID", str(int(pid)), "/F"],
                capture_output=True, creationflags=NO_WINDOW, timeout=10
            )
    except Exception:
        pass


ROBLOX_SETTINGS_FILE = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Roblox", "GlobalBasicSettings_13.xml")
ROBLOX_VERSIONS_DIR = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Roblox", "Versions")
ROBLOX_LOG_DIR = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Roblox", "logs")
CUSTOM_FLAGS_FILE = os.path.join(DATA_DIR, "custom_flags.json")
MANAGED_MARK = "ClientAppSettings.managed.json"


def slim_down_client(pid, trim=True):
    """Lean client: lower the process priority and (optionally) trim its working set so Windows can
    hand unused memory to the other clients. Returns True when the process could be adjusted."""
    if os.name != "nt":
        return False
    try:
        kernel = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        kernel.OpenProcess.restype = wintypes.HANDLE
        kernel.SetPriorityClass.argtypes = [wintypes.HANDLE, wintypes.DWORD]
        kernel.SetPriorityClass.restype = wintypes.BOOL
        kernel.CloseHandle.argtypes = [wintypes.HANDLE]
        # PROCESS_SET_QUOTA | PROCESS_SET_INFORMATION | PROCESS_QUERY_INFORMATION
        handle = kernel.OpenProcess(0x0100 | 0x0200 | 0x0400, False, int(pid))
        if not handle:
            return False
        try:
            kernel.SetPriorityClass(handle, 0x00004000)  # BELOW_NORMAL_PRIORITY_CLASS
            if trim:
                psapi = ctypes.WinDLL("psapi", use_last_error=True)
                psapi.EmptyWorkingSet.argtypes = [wintypes.HANDLE]
                psapi.EmptyWorkingSet(handle)
        finally:
            kernel.CloseHandle(handle)
        return True
    except Exception:
        return False


# ----- performance profile: fast flags (Bloxstrap / Fishstrap style) + Roblox's own settings file -----
# Roblox only honours fast flags on its own allow-list and silently ignores the rest.
# Stable flags only: these never stop a client from loading.
POTATO_FLAGS = {
    "DFFlagTextureQualityOverrideEnabled": True,
    "DFIntTextureQualityOverride": 0,
    "DFIntDebugFRMQualityLevelOverride": 1,
    "FIntRenderShadowIntensity": 0,
    "FFlagDisablePostFx": True,
    "FIntFRMMinGrassDistance": 0,
    "FIntFRMMaxGrassDistance": 0,
    "FIntRenderGrassDetailStrands": 0,
    "FFlagGlobalWindActivated": False,
    "FFlagGlobalWindRendering": False,
    "DFIntCSGLevelOfDetailSwitchingDistance": 0,
    "DFIntCSGLevelOfDetailSwitchingDistanceL12": 0,
    "DFIntCSGLevelOfDetailSwitchingDistanceL23": 0,
    "DFIntCSGLevelOfDetailSwitchingDistanceL34": 0,
    "FIntDebugForceMSAASamples": 1,
    "FIntRobloxGuiBlurIntensity": 0,
    "FIntRomarkStartWithGraphicQualityLevel": 1,
    # Lower-RAM extras: shrink the FPS target so the GPU/CPU chews less,
    # drop particle/lighting detail, cut telemetry and light grid work.
    "DFIntTaskSchedulerTargetFps": 30,
    "FIntTerrainOTAMinUploadFPS": 10,
    "FFlagDebugDisableTelemetryV2": True,
    "FFlagDebugDisableTelemetryEphemeralCounter": True,
    "FFlagDebugDisableTelemetryEphemeralStat": True,
    "FFlagDebugDisableTelemetryEventIngest": True,
    "FFlagDebugDisableTelemetryPoint": True,
    "FFlagDebugDisableTelemetryV2Counter": True,
    "FFlagDebugDisableTelemetryV2Event": True,
    "FFlagDebugDisableTelemetryV2Stat": True,
    "FIntRenderLightGridMaxCPUResolution": 32,
    "FFlagNewLightAttenuation": False,
    "DFIntMaxNumberOfParticlesForSound": 0,
    "FIntRenderGrassHeightScaler": 0,
}
# Aggressive flags: they can leave the client stuck on loading screens or crashing on some PCs, so they only apply when
# the "Extra low graphics" pack is switched on.
POTATO_RISKY = {
    "FFlagDebugDisableOTAMaterialTexture": True,
    "FFlagDebugSkyGray": True,
    "DFFlagDebugPauseVoxelizer": True,
    "DFIntCullFactorPixelThresholdShadowMapHighQuality": 2147483647,
    "DFIntCullFactorPixelThresholdShadowMapLowQuality": 2147483647,
    "FIntSSAOMipLevels": 0,
    "DFIntMaxFrameBufferSize": 4,
    "DFIntRenderClampRoughnessMax": -640000000,
    "FIntTerrainArraySliceSize": 0,
    "FIntDebugTextureManagerSkipMips": 8,
}
# Accounts without the rocket: highest graphics and an unlocked frame rate.
HIGH_FPS = 120
HIGH_FLAGS = {
    "DFIntTaskSchedulerTargetFps": HIGH_FPS,
    "FFlagTaskSchedulerLimitTargetFpsTo2402": False,
    "DFIntDebugFRMQualityLevelOverride": 21,
}
_XML_KINDS = "int|token|float|string|bool"


def roblox_client_dirs():
    """The newest installed Roblox player folders (Roblox keeps a new one after every update)."""
    found = []
    try:
        for name in os.listdir(ROBLOX_VERSIONS_DIR):
            folder = os.path.join(ROBLOX_VERSIONS_DIR, name)
            if os.path.isfile(os.path.join(folder, "RobloxPlayerBeta.exe")):
                found.append(folder)
    except OSError:
        return []
    found.sort(key=os.path.getmtime, reverse=True)
    return found[:3]


def _xml_value(text, name):
    m = re.search(r'<(?:%s) name="%s">([^<]*)</' % (_XML_KINDS, re.escape(name)), text)
    return m.group(1) if m else None


def _xml_set(text, name, value, create=None):
    pattern = re.compile(r'(<(%s) name="%s">)[^<]*(</\2>)' % (_XML_KINDS, re.escape(name)))
    if pattern.search(text):
        return pattern.sub(lambda m: m.group(1) + str(value) + m.group(3), text)
    if create and "</Properties>" in text:
        return text.replace("</Properties>", f'<{create} name="{name}">{value}</{create}></Properties>', 1)
    return text


def load_custom_flags():
    try:
        with open(CUSTOM_FLAGS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def save_custom_flags(text):
    """Validate and store the user's own fast flags. -> (ok, message)"""
    text = (text or "").strip()
    if not text:
        data = {}
    else:
        try:
            data = json.loads(text)
        except ValueError as exc:
            return False, f"not valid JSON ({exc})"
        if not isinstance(data, dict):
            return False, "must be a JSON object like {\"FFlagName\": true}"
        for key, value in data.items():
            if not re.fullmatch(r"[A-Za-z0-9_]{3,120}", str(key)):
                return False, f"bad flag name: {key}"
            if not isinstance(value, (bool, int, str)):
                return False, f"bad value for {key}"
    try:
        os.makedirs(os.path.dirname(CUSTOM_FLAGS_FILE), exist_ok=True)
        with open(CUSTOM_FLAGS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except OSError as exc:
        return False, f"could not save ({exc})"
    return True, f"{len(data)} flag(s) saved"


def apply_profile(perf, fps_cap=None, mute=False, custom=None, high=False):
    """Prepare Roblox's settings for the client that is about to start (it reads them once at start-up).
    perf: lowest graphics (fast flags + graphics level + frame-rate cap); otherwise the user's own values are put
    back. Only values we wrote ourselves are ever touched. -> (changed, message); '' when nothing was needed."""
    wanted = dict(custom or {})
    if perf:
        wanted.update(POTATO_FLAGS)
    elif high:
        wanted.update(HIGH_FLAGS)
    changed, problems = 0, []
    for folder in roblox_client_dirs():
        settings_dir = os.path.join(folder, "ClientSettings")
        path = os.path.join(settings_dir, "ClientAppSettings.json")
        mark = os.path.join(settings_dir, MANAGED_MARK)
        try:
            data = {}
            if os.path.isfile(path):
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if not isinstance(data, dict):
                    raise ValueError("not a JSON object")
            managed = []
            if os.path.isfile(mark):
                try:
                    with open(mark, "r", encoding="utf-8") as f:
                        managed = [str(k) for k in json.load(f)]
                except (OSError, ValueError):
                    managed = []
            before = dict(data)
            for key in managed:
                if key not in wanted:
                    data.pop(key, None)
            data.update(wanted)
            if data != before:
                if data:
                    os.makedirs(settings_dir, exist_ok=True)
                    tmp = path + ".tmp"
                    with open(tmp, "w", encoding="utf-8") as f:
                        json.dump(data, f, indent=2)
                    os.replace(tmp, path)
                elif os.path.isfile(path):
                    os.remove(path)
                changed += 1
            if sorted(managed) != sorted(wanted):
                if wanted:
                    os.makedirs(settings_dir, exist_ok=True)
                    with open(mark, "w", encoding="utf-8") as f:
                        json.dump(sorted(wanted), f)
                elif os.path.isfile(mark):
                    os.remove(mark)
        except (OSError, ValueError) as exc:
            problems.append(f"{os.path.basename(folder)}: {exc}")

    path = ROBLOX_SETTINGS_FILE
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                text = f.read()
            backup, state_file = path + ".redshift.bak", path + ".redshift.state"
            try:
                with open(state_file, "r", encoding="utf-8") as f:
                    state = {str(k): str(v) for k, v in json.load(f).items()}
            except (OSError, ValueError, AttributeError):
                state = {}
            if os.path.isfile(backup):
                with open(backup, "r", encoding="utf-8") as f:
                    original = f.read()
            else:
                original = text
            new_text = text

            def put(name, value, create=None):
                nonlocal new_text
                new_text = _xml_set(new_text, name, value, create)
                state[name] = str(value)

            def restore(name):
                nonlocal new_text
                if name in state and _xml_value(new_text, name) == state[name]:
                    old = _xml_value(original, name)
                    if old is not None:
                        new_text = _xml_set(new_text, name, old)
                state.pop(name, None)
            if perf:
                for name in ("GraphicsQualityLevel", "SavedQualityLevel"):
                    if _xml_value(new_text, name) is not None:
                        put(name, 1)
                if fps_cap:
                    put("FramerateCap", int(fps_cap), "int")
                else:
                    restore("FramerateCap")
            elif high:
                for name in ("GraphicsQualityLevel", "SavedQualityLevel"):
                    if _xml_value(new_text, name) is not None:
                        put(name, 10)
                put("FramerateCap", HIGH_FPS, "int")
            else:
                for name in ("GraphicsQualityLevel", "SavedQualityLevel", "FramerateCap"):
                    restore(name)
            if not high and _xml_value(original, "FramerateCap") is None and _xml_value(new_text, "FramerateCap") == str(HIGH_FPS):
                put("FramerateCap", 240, "int")  # a cap we set earlier must not stay on a client that is not 'high'  
            if mute:
                put("MasterVolume", 0, "float")
            else:
                restore("MasterVolume")
            if new_text != text:
                if not os.path.exists(backup):
                    shutil.copy2(path, backup)
                tmp = path + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(new_text)
                os.replace(tmp, path)
                changed += 1
            with open(state_file, "w", encoding="utf-8") as f:
                json.dump(state, f)
    except OSError as exc:
        problems.append(f"Roblox settings: {exc}")
    if problems:
        return bool(changed), "could not finish (" + "; ".join(problems) + ")."
    if changed:
        return True, ("performance profile ready (lowest graphics)." if perf else
                      (f"high profile ready (highest graphics, {HIGH_FPS} FPS)." if high else "normal profile ready."))
    return False, ""


# ----- multi-instance: hold Roblox's single-instance mutex while this program runs -----
MULTI = {"ok": None, "note": "not checked yet"}
_event_handle = None


def hold_singleton_mutex():
    """Lets several Roblox clients run side by side. Needs to be the first to create the mutex, so Roblox must not
    have been running before this program started (MULTI tells what happened)."""
    global _mutex_handle, _event_handle
    MULTI["ok"], MULTI["note"] = False, "Windows only"
    if os.name != "nt":
        return
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
        k.CreateMutexW.restype = wintypes.HANDLE
        k.CreateEventW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.BOOL, wintypes.LPCWSTR]
        k.CreateEventW.restype = wintypes.HANDLE
        k.CloseHandle.argtypes = [wintypes.HANDLE]
        for old in (_mutex_handle, _event_handle):
            if old:
                k.CloseHandle(old)
        ctypes.set_last_error(0)
        _mutex_handle = k.CreateMutexW(None, True, "ROBLOX_singletonMutex")
        error = ctypes.get_last_error()
        _event_handle = k.CreateEventW(None, False, False, "ROBLOX_singletonEvent")
        if not _mutex_handle:
            MULTI["ok"], MULTI["note"] = False, "could not create the Roblox mutex"
        elif error == 183:  # ERROR_ALREADY_EXISTS: a Roblox client got there first
            MULTI["ok"], MULTI["note"] = False, "Roblox was already running - close it, then press Fix"
        else:
            MULTI["ok"], MULTI["note"] = True, "ready"
    except Exception as exc:
        _mutex_handle = None
        MULTI["ok"], MULTI["note"] = False, f"mutex error: {exc}"


def repair_multi_instance():
    """Close every Roblox client (waiting until Windows has really let go of them) and take the single-instance
    mutex again. -> True when multi-instance works."""
    if os.name == "nt":
        for _attempt in range(4):
            for exe in (PROC_NAME, "RobloxPlayerLauncher.exe", "RobloxCrashHandler.exe"):
                try:
                    subprocess.run(["taskkill", "/IM", exe, "/F", "/T"], capture_output=True,
                                   creationflags=NO_WINDOW, timeout=15)
                except Exception:
                    pass
            end = time.time() + 6
            while time.time() < end:
                left = native_roblox_pids()
                if not left:
                    break
                time.sleep(0.3)
            time.sleep(0.4)
            retake = hold_singleton_mutex
            retake()
            if MULTI["ok"]:
                break
            time.sleep(1.0)
        return bool(MULTI["ok"])
    retake = hold_singleton_mutex
    retake()
    return bool(MULTI["ok"])


# ----- window tools -----
def tile_roblox_windows(pids, tiny=False):
    """Arrange the Roblox windows of the given processes in a neat grid on the primary screen. -> windows moved"""
    if os.name != "nt":
        return 0
    wanted = {int(p) for p in pids}
    if not wanted:
        return 0
    try:
        u32 = ctypes.WinDLL("user32", use_last_error=True)
        enum_proc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        u32.EnumWindows.argtypes = [enum_proc, wintypes.LPARAM]
        u32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
        u32.IsWindowVisible.argtypes = [wintypes.HWND]
        u32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
        u32.MoveWindow.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, wintypes.BOOL]
        u32.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
        u32.SystemParametersInfoW.argtypes = [ctypes.c_uint, ctypes.c_uint, ctypes.c_void_p, ctypes.c_uint]
        found = []

        def cb(hwnd, _l):
            pid = wintypes.DWORD()
            u32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value in wanted and u32.IsWindowVisible(hwnd):
                buf = ctypes.create_unicode_buffer(256)
                u32.GetClassNameW(hwnd, buf, 256)
                if buf.value == "WINDOWSCLIENT":
                    found.append((pid.value, hwnd))
            return True
        proc = enum_proc(cb)
        u32.EnumWindows(proc, 0)
        if not found:
            return 0
        found.sort()
        area = wintypes.RECT()
        u32.SystemParametersInfoW(0x0030, 0, ctypes.byref(area), 0)  # SPI_GETWORKAREA
        width, height = area.right - area.left, area.bottom - area.top
        n = len(found)
        cols = int(math.ceil(math.sqrt(n * width / max(1, height))))
        cols = max(1, min(n, cols))
        rows = int(math.ceil(n / cols))
        cell_w, cell_h = width // cols, height // rows
        if tiny:  # small windows render far fewer pixels: fixed small cells, as many per row as fit
            cell_w, cell_h = 420, 280
            cols = max(1, min(n, width // cell_w))
        for index, (_pid, hwnd) in enumerate(found):
            u32.ShowWindow(hwnd, 9)  # SW_RESTORE
            u32.MoveWindow(hwnd, area.left + (index % cols) * cell_w, area.top + (index // cols) * cell_h,
                           cell_w, cell_h, True)
        return n
    except Exception:
        return 0


def clear_roblox_cache():
    """Delete Roblox's log files and temp files (never settings or game files). -> (files, bytes)"""
    count = size = 0
    for folder in (ROBLOX_LOG_DIR, os.path.join(os.environ.get("TEMP", ""), "Roblox")):
        if not folder or not os.path.isdir(folder):
            continue
        for root, _dirs, files in os.walk(folder):
            for name in files:
                path = os.path.join(root, name)
                try:
                    length = os.path.getsize(path)
                    os.remove(path)
                    count += 1
                    size += length
                except OSError:
                    pass  # in use by a running client
    return count, size


def open_in_edge(url):
    """Open a page in Microsoft Edge only (never the default browser). -> True when Edge was started"""
    edge = find_edge()
    if not edge:
        return False
    try:
        subprocess.Popen([edge, url])
        return True
    except OSError:
        return False


def free_memory(pids):
    """Trim the working set of the given clients. Returns how many were trimmed."""
    done = 0
    for pid in pids:
        try:
            slim_down_client(pid, trim=True)
            done += 1
        except Exception:
            pass
    return done


class _ProcEntry(ctypes.Structure):
    _fields_ = [("dwSize", wintypes.DWORD), ("cntUsage", wintypes.DWORD), ("th32ProcessID", wintypes.DWORD),
                ("th32DefaultHeapID", ctypes.c_size_t), ("th32ModuleID", wintypes.DWORD),
                ("cntThreads", wintypes.DWORD), ("th32ParentProcessID", wintypes.DWORD),
                ("pcPriClassBase", ctypes.c_long), ("dwFlags", wintypes.DWORD),
                ("szExeFile", ctypes.c_wchar * 260)]


_NATIVE = {"k": None, "bad": False}


def native_roblox_pids():
    """Running Roblox client PIDs straight from Windows (about a millisecond, no tasklist process).
    None when it is not available, so the caller falls back to tasklist."""
    if os.name != "nt" or _NATIVE["bad"]:
        return None
    try:
        k = _NATIVE["k"]
        if k is None:
            k = ctypes.WinDLL("kernel32", use_last_error=True)
            k.CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
            k.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
            k.Process32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(_ProcEntry)]
            k.Process32FirstW.restype = wintypes.BOOL
            k.Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(_ProcEntry)]
            k.Process32NextW.restype = wintypes.BOOL
            k.CloseHandle.argtypes = [wintypes.HANDLE]
            _NATIVE["k"] = k
        snap = k.CreateToolhelp32Snapshot(0x2, 0)
        if snap in (None, 0, ctypes.c_void_p(-1).value):
            return None
        pids = set()
        try:
            entry = _ProcEntry()
            entry.dwSize = ctypes.sizeof(_ProcEntry)
            ok = k.Process32FirstW(snap, ctypes.byref(entry))
            wanted = PROC_NAME.lower()
            while ok:
                if entry.szExeFile.lower() == wanted:
                    pids.add(int(entry.th32ProcessID))
                ok = k.Process32NextW(snap, ctypes.byref(entry))
        finally:
            k.CloseHandle(snap)
        return pids
    except Exception:
        _NATIVE["bad"] = True
        return None


# Extra fast-flag packs (each one switch in Tune). Roblox ignores flags it does not know, so a pack can never break a client.
FLAG_PACKS = {
    "extralow": ("Extra low graphics", "Even uglier and lighter. Can make loading slower or crash on some PCs - switch it off if a client hangs.", dict(POTATO_RISKY)),
    "telemetry": ("Telemetry off", "Stops Roblox's analytics counters, events and stats.", {
        "FFlagDebugDisableTelemetryEphemeralCounter": True,
        "FFlagDebugDisableTelemetryEphemeralStat": True,
        "FFlagDebugDisableTelemetryEventIngest": True,
        "FFlagDebugDisableTelemetryPoint": True,
        "FFlagDebugDisableTelemetryV2Counter": True,
        "FFlagDebugDisableTelemetryV2Event": True,
        "FFlagDebugDisableTelemetryV2Stat": True,
    }),
    "network": ("Low network load", "Slower physics updates sent to the server, less traffic per client.", {
        "DFIntS2PhysicsSenderRate": 15,
    }),
    "d3d11": ("Direct3D 11", "Forces the Direct3D 11 renderer.", {
        "FFlagDebugGraphicsPreferD3D11": True,
    }),
    "input": ("Alt+Enter off", "No accidental fullscreen switch when you press Alt+Enter.", {
        "FFlagHandleAltEnterFullscreenManually": False,
    }),
}


def pack_flags(enabled):
    """Merged flags of the enabled packs."""
    merged = {}
    for key in enabled:
        if key in FLAG_PACKS:
            merged.update(FLAG_PACKS[key][2])
    return merged


# Login method (Edge): how careful or how quick the browser login is.
LOGIN_MODE = {"mode": "safe"}
LOGIN_PROFILES = {
    # smart: the real profile is chosen at every login (see smart_login); this is the fallback
    "smart": {"fresh": False, "shared": False, "settle": 0.4, "ready": 15, "poll": 0.25},
    # slow: like safe, but with much longer waits
    "slow": {"fresh": False, "shared": False, "settle": 2.5, "ready": 45, "poll": 0.6},
    # safe: a clean Edge restart for every account, a still valid saved Edge session is reused, patient waits
    "safe": {"fresh": False, "shared": False, "settle": 1.2, "ready": 25, "poll": 0.4},
    # normal: a fresh Edge per account, a still valid Edge session is reused
    "normal": {"fresh": False, "shared": False, "settle": 0.4, "ready": 15, "poll": 0.25},
    # fast: one Edge for all accounts, short waits
    "fast": {"fresh": False, "shared": True, "settle": 0.1, "ready": 12, "poll": 0.12},
}


def check_network():
    """-> (state, milliseconds): ok / slow / roblox (Roblox unreachable, internet fine) / offline."""
    import socket

    def probe(host, timeout):
        started = time.monotonic()
        try:
            with socket.create_connection((host, 443), timeout=timeout):
                return (time.monotonic() - started) * 1000.0
        except OSError:
            return None
    ms = probe("www.roblox.com", 5)
    if ms is not None:
        return ("slow" if ms > 1500 else "ok"), int(ms)
    if any(probe(host, 3) is not None for host in ("1.1.1.1", "8.8.8.8", "www.microsoft.com")):
        return "roblox", 0
    return "offline", 0


NET_TEXT = {
    "offline": ("No internet connection", "Your internet connection looks down - check your network."),
    "roblox": ("Roblox unreachable", "Roblox cannot be reached right now - the site may be down or blocked."),
    "slow": ("Slow connection", "Your connection is slow, so joining can take longer."),
    "ok": ("", ""),
}


class _PMC(ctypes.Structure):
    _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD),
                ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t)]


def process_memory_mb(pid):
    """Working set of a process in MB (None when it cannot be read)."""
    if os.name != "nt":
        return None
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
        k.OpenProcess.restype = wintypes.HANDLE
        k.CloseHandle.argtypes = [wintypes.HANDLE]
        psapi = ctypes.WinDLL("psapi", use_last_error=True)
        psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(_PMC), wintypes.DWORD]
        psapi.GetProcessMemoryInfo.restype = wintypes.BOOL
        handle = k.OpenProcess(0x1000 | 0x0400, False, int(pid))  # QUERY_LIMITED_INFORMATION | QUERY_INFORMATION
        if not handle:
            return None
        try:
            counters = _PMC()
            counters.cb = ctypes.sizeof(_PMC)
            if not psapi.GetProcessMemoryInfo(handle, ctypes.byref(counters), counters.cb):
                return None
            return int(counters.WorkingSetSize / 1048576)
        finally:
            k.CloseHandle(handle)
    except Exception:
        return None


def _login_page_problem(text):
    """Plain-language reason found in the visible text of Roblox's login page ('' when there is none)."""
    if "incorrect username or password" in text:
        return "Wrong username or password - remove the account and add it again with the right password."
    if "too many attempts" in text or "too many requests" in text:
        return "Roblox says too many attempts - wait a few minutes before trying again."
    if "account has been locked" in text or "account is locked" in text:
        return "This account is locked by Roblox."
    if "verification code" in text or "enter the code" in text or "2-step" in text:
        return "Roblox asks for a verification code - enter it in the Edge window."
    return ""


def lookup_game(place_id):
    """{'name', 'playing'} of a Roblox game by its place ID (None when it does not exist or Roblox is unreachable)."""
    try:
        r = requests.get(f"https://apis.roblox.com/universes/v1/places/{int(place_id)}/universe", timeout=10)
        universe = r.json().get("universeId") if r.status_code == 200 else None
        if not universe:
            return None
        r = requests.get(f"https://games.roblox.com/v1/games?universeIds={int(universe)}", timeout=10)
        data = (r.json().get("data") or []) if r.status_code == 200 else []
        if not data:
            return None
        return {"name": str(data[0].get("name", "")), "playing": int(data[0].get("playing", 0) or 0)}
    except Exception:
        return None


def parse_game_id(text):
    """Place ID from a number or a roblox.com link ('' / bad input -> None)."""
    text = (text or "").strip()
    if not text:
        return None
    if text.isdigit():
        value = int(text)
        return value if value > 0 else None
    match = re.search(r"/games/(\d+)", text) or re.search(r"[?&]placeId=(\d+)", text, re.I)
    return int(match.group(1)) if match else None


def parse_server_id(text):
    """Server (job) ID: a UUID. '' -> ('', True); bad input -> (None, False)."""
    text = (text or "").strip()
    if not text:
        return "", True
    if re.fullmatch(r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}", text):
        return text.lower(), True
    return None, False


def fmt_clock(seconds):
    seconds = max(0, int(seconds))
    return f"{seconds // 60:02d}:{seconds % 60:02d}"


# what each type means and roughly how long one account takes (the real times are learned while launching)
SPEED_EST = {"smart": 35, "slow": 75, "safe": 40, "fast": 25, "instant": 18}
SPEED_TEXT = {"smart": "Picks the speed each time from your PC, connection and number of accounts.",
              "slow": "Very long pauses and patient waits. For weak PCs or a slow connection.",
              "safe": "Longest pauses between starts. Most reliable.",
              "fast": "Short pauses. A good balance.",
              "instant": "Shortest pauses. Needs a fast PC."}
LOGIN_EST = {"smart": 10, "slow": 22, "safe": 12, "normal": 8, "fast": 4}
LOGIN_TEXT = {"smart": "Picks the method each time: careful after a failed login or on a slow connection, quick for many logins.",
              "slow": "Edge restarts for every account and waits as long as needed. Best for a slow PC or connection.",
              "safe": "Edge restarts for every account and waits patiently. Most reliable.",
              "normal": "Edge restarts for every account, a saved session is reused.",
              "fast": "One Edge window for all accounts. Quickest."}


# ----- smart modes and automatic repairs -----
def memory_status():
    """-> (total GB, free GB); (0, 0) when Windows cannot tell."""
    if os.name != "nt":
        return 0.0, 0.0
    try:
        class _MemStatus(ctypes.Structure):
            _fields_ = [("dwLength", wintypes.DWORD), ("dwMemoryLoad", wintypes.DWORD),
                        ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                        ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                        ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                        ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
        status = _MemStatus()
        status.dwLength = ctypes.sizeof(_MemStatus)
        ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status))
        return status.ullTotalPhys / 2 ** 30, status.ullAvailPhys / 2 ** 30
    except Exception:
        return 0.0, 0.0


def smart_speed(accounts, net_state, free_gb, cores):
    """Launch speed chosen from the PC, the connection and the number of accounts. -> (speed, reason)"""
    if net_state in ("offline", "roblox"):
        return "slow", "Roblox is hard to reach right now"
    if net_state == "slow":
        return "slow", "slow connection"
    if free_gb and free_gb < 2.5:
        return "slow", f"only {free_gb:.1f} GB memory free"
    if (free_gb and free_gb < 5) or cores <= 4:
        return "safe", "a modest PC"
    if accounts >= 6:
        return "safe", f"{accounts} accounts at once"
    if accounts <= 2 and cores >= 8 and (not free_gb or free_gb >= 8):
        return "instant", "strong PC, few accounts"
    return "fast", "balanced PC and connection"


def smart_login(needed, net_state, failures):
    """Login method chosen for the logins that are needed right now. -> (mode, reason)"""
    if failures:
        return "slow", "the last login did not finish"
    if net_state != "ok":
        return "slow", "slow connection"
    if needed >= 3:
        return "fast", f"{needed} logins, one Edge for all"
    return "normal", "few logins"


def repair_roblox_settings():
    """Move a damaged ClientAppSettings.json out of the way (Roblox would ignore everything). -> files repaired"""
    fixed = 0
    for folder in roblox_client_dirs():
        path = os.path.join(folder, "ClientSettings", "ClientAppSettings.json")
        if not os.path.isfile(path):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                ok = isinstance(json.load(f), dict)
        except (OSError, ValueError):
            ok = False
        if not ok:
            try:
                os.replace(path, path + ".broken")
                fixed += 1
            except OSError:
                pass
    return fixed


def sync_clock():
    """Ask Windows to sync its clock (works only with administrator rights). -> True when it worked"""
    if os.name != "nt":
        return False
    try:
        r = subprocess.run(["w32tm", "/resync"], capture_output=True, creationflags=NO_WINDOW, timeout=25)
        return r.returncode == 0
    except Exception:
        return False

# --------------------------------------------------------------------------
# Roblox client state: working or showing an error?
# --------------------------------------------------------------------------
_CLIENT_ERROR_CODES = {
    "267": "Kicked by the game",
    "268": "Kicked: unexpected client behavior",
    "273": "Disconnected: account joined from another device",
    "277": "Lost connection to the game",
    "279": "Could not connect to the game",
    "403": "Authentication failed",
}
_CLIENT_ERROR_WORDS = (
    (("authentication", "authentifizierung", "log in again", "erneut an"), "Authentication error (login rejected)"),
    (("banned", "gesperrt", "terminated"), "Account banned or restricted"),
    (("kicked", "removed from", "entfernt", "gekickt"), "Kicked from the experience"),
    (("disconnected", "connection lost", "lost connection", "verbindung", "getrennt", "disconnect"),
     "Disconnected from the game"),
    (("out of date", "veraltet", "needs to update", "update required"), "Roblox needs an update"),
    (("not available", "nicht verfügbar", "no longer available", "unavailable"), "Experience or server not available"),
    (("crash", "absturz", "unexpected error", "unerwarteter fehler"), "Roblox crashed"),
)


def describe_client_error(text):
    """Turn the text of a Roblox error window into a short, readable reason (None = not an error)."""
    t = (text or "").lower()
    if not t.strip():
        return None
    match = re.search(r"(?:error code|fehlercode|code)\D{0,3}(\d{3})", t)
    code = match.group(1) if match else None
    if code in _CLIENT_ERROR_CODES:
        return f"{_CLIENT_ERROR_CODES[code]} ({code})"
    for words, label in _CLIENT_ERROR_WORDS:
        if any(word in t for word in words):
            return label + (f" ({code})" if code else "")
    return None


def windows_of_pids(pids):
    """Top-level windows owned by the given processes (Windows only):
    {pid: [{'class', 'title', 'visible', 'text'}]}. 'text' is the message text of dialog boxes."""
    result = {int(p): [] for p in pids}
    if os.name != "nt" or not result:
        return result
    try:
        u32 = ctypes.WinDLL("user32", use_last_error=True)  # own handle: no argtypes side effects elsewhere
        enum_proc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)
        u32.EnumWindows.argtypes = [enum_proc, wintypes.LPARAM]
        u32.EnumChildWindows.argtypes = [wintypes.HWND, enum_proc, wintypes.LPARAM]
        u32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
        u32.GetWindowTextLengthW.argtypes = [wintypes.HWND]
        u32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
        u32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
        u32.IsWindowVisible.argtypes = [wintypes.HWND]

        def text_of(hwnd):
            n = u32.GetWindowTextLengthW(hwnd)
            buf = ctypes.create_unicode_buffer(n + 1)
            u32.GetWindowTextW(hwnd, buf, n + 1)
            return buf.value

        def class_of(hwnd):
            buf = ctypes.create_unicode_buffer(256)
            u32.GetClassNameW(hwnd, buf, 256)
            return buf.value

        def child_text(hwnd):
            parts = []

            def child_cb(h, _l):
                value = text_of(h)
                if value:
                    parts.append(value)
                return True
            proc = enum_proc(child_cb)
            u32.EnumChildWindows(hwnd, proc, 0)
            return " ".join(parts)[:400]

        def top_cb(hwnd, _l):
            pid = wintypes.DWORD()
            u32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value in result:
                cls = class_of(hwnd)
                result[pid.value].append({
                    "class": cls, "title": text_of(hwnd), "visible": bool(u32.IsWindowVisible(hwnd)),
                    "text": child_text(hwnd) if cls == "#32770" else "",
                })
            return True

        top_proc = enum_proc(top_cb)
        u32.EnumWindows(top_proc, 0)
    except Exception:
        pass
    return result


def classify_client(alive, hung, age, windows, joined=False, presence=None):
    """Decide whether a Roblox client WORKS or shows a problem.
    -> (state, text, strong); state is closed / hung / error / dialog / starting / unknown / lobby / working.
    'strong' means the evidence is clear enough to act on (restart); everything else is only displayed."""
    if not alive:
        return "closed", "Closed or crashed", True
    if hung:
        return "hung", "Not responding", True
    main_window = False
    for window in windows or []:
        if not window.get("visible"):
            continue
        title = (window.get("title") or "").strip()
        blob = f"{title} {window.get('text', '')}"
        is_dialog = window.get("class") == "#32770"
        is_main = title.lower() == "roblox" and not is_dialog
        if is_main:
            main_window = True
            continue
        reason = describe_client_error(blob)
        if reason:
            return "error", reason, True
        if is_dialog:
            return "dialog", f"Message open: {blob.strip()[:50] or 'unknown'}", False
    if not main_window:
        if age < 60:
            return "starting", "Starting ...", False
        return "unknown", "No window yet", False
    if joined and presence == 2:
        return "working", "In game", False
    if joined and presence is not None and presence != 2 and age > 120:
        return "lobby", "Not in a game", False
    return "working", "Running", False


def client_windows(pid_list):
    """One call for all tracked clients: {pid: [window, ...]}"""
    try:
        return windows_of_pids(pid_list)
    except Exception:
        return {int(p): [] for p in pid_list}


# --------------------------------------------------------------------------
# One waiting line for the account tools
# --------------------------------------------------------------------------
class ActionQueue:
    """Runs the account tools (outfit, bio, display name, follow, friends) one after another.
    A request made while another tool is working is shown at once and starts by itself afterwards."""

    class Job:
        def __init__(self, title, kind, fn, args):
            self.title, self.kind, self.fn, self.args = title, kind, fn, args
            self.cancel = threading.Event()
            self.total = 0
            self.done = 0
            self.started = None
            self.number = 0

    def __init__(self, on_change, log):
        self._lock = threading.Lock()
        self._pending = collections.deque()
        self._current = None
        self._worker = None
        self._idle = threading.Event()
        self._idle.set()
        self._on_change = on_change
        self._log = log
        self._counter = 0

    def _notify(self):
        try:
            self._on_change()
        except Exception:
            pass

    def submit(self, title, kind, fn, *args):
        """Put a tool in line. Returns how many tools are ahead of it: 0 = starts right now."""
        with self._lock:
            ahead = len(self._pending) + (1 if self._current is not None else 0)
            self._counter += 1
            job = self.Job(title, kind, fn, args)
            job.number = self._counter
            self._pending.append(job)
            self._idle.clear()
            if self._worker is None:
                self._worker = threading.Thread(target=self._run, name="CrimsonActionQueue", daemon=True)
                self._worker.start()
        self._notify()
        return ahead

    def _run(self):
        while True:
            with self._lock:
                if not self._pending:
                    self._current = None
                    self._worker = None
                    self._idle.set()
                    break
                job = self._pending.popleft()
                job.started = time.time()
                self._current = job
            self._notify()
            try:
                job.fn(*job.args)
            except Exception as exc:
                self._log(f"{job.title}: error - {exc}")
            self._notify()
        self._notify()

    def current_cancel(self):
        job = self._current
        return job.cancel if job else None

    def cancelled(self):
        job = self._current
        return bool(job and job.cancel.is_set())

    def snapshot(self):
        with self._lock:
            job = self._current
            return {
                "current": None if job is None else {
                    "title": job.title, "kind": job.kind, "done": job.done, "total": job.total,
                    "started": job.started, "number": job.number},
                "waiting": [j.title for j in self._pending],
            }

    def ticker(self, total):
        """Set the number of steps of the running tool; the returned function counts one step done."""
        job = self._current
        if job is not None:
            job.total, job.done = int(total), 0
        lock = threading.Lock()

        def tick(n=1):
            if job is None:
                return
            with lock:
                job.done = min(job.total, job.done + n)
            self._notify()
        self._notify()
        return tick

    def stop(self):
        """Cancel the running tool and drop everything that waits. Returns how many waiting tools were dropped."""
        with self._lock:
            dropped = len(self._pending)
            self._pending.clear()
            if self._current is not None:
                self._current.cancel.set()
        self._notify()
        return dropped

    def wait_idle(self, timeout):
        return self._idle.wait(timeout)

    def busy(self):
        return not self._idle.is_set()


# --------------------------------------------------------------------------
# Roblox web API
# --------------------------------------------------------------------------
class RateGate:
    """One shared 'wait' per Roblox host: when any call gets a rate limit (HTTP 429), every other call to that
    host pauses too, then everything continues automatically - no retry storm, no error."""

    def __init__(self):
        self.lock = threading.Lock()
        self.until = {}
        self.last_log = {}
        self.cancel = lambda: False
        self.log = lambda message: None

    def wait(self, host):
        while True:
            with self.lock:
                left = self.until.get(host, 0) - time.time()
            if left <= 0 or self.cancel():
                return
            time.sleep(min(0.4, left))

    def hit(self, host, seconds):
        seconds = max(1.0, min(90.0, float(seconds)))
        with self.lock:
            end = time.time() + seconds
            if end > self.until.get(host, 0):
                self.until[host] = end
            now = time.time()
            show = now - self.last_log.get(host, 0) > 8
            if show:
                self.last_log[host] = now
        if show:
            self.log(f"Roblox rate limit on {host} - waiting {seconds:.0f} s, then continuing automatically.")


_RATE = RateGate()
RATE_TEXT_RE = re.compile(r"too many|try again later|throttl|rate limit|zu viele", re.I)


class RobloxSession:
    def __init__(self, cookie: str):
        self.s = requests.Session()
        adapter = requests.adapters.HTTPAdapter(pool_connections=32, pool_maxsize=32)
        self.s.mount("https://", adapter)  # many parallel calls reuse open connections
        self.s.cookies.set(".ROBLOSECURITY", cookie, domain=".roblox.com")
        self.s.headers["User-Agent"] = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"
        self.csrf = None
        self.last_auth_state = "unknown"
        self.last_status = None

    def _refresh_csrf(self):
        r = self.s.post("https://auth.roblox.com/v2/logout", timeout=15)
        self.csrf = r.headers.get("x-csrf-token")

    def req(self, method, url, retries=3, **kw):
        """Request with CSRF handling and automatic retries (network errors, 429, 5xx)."""
        r = None
        host = urllib.parse.urlparse(url).hostname or "roblox.com"
        rate_waits, attempt = 0, 0
        while attempt < retries:
            attempt += 1
            _RATE.wait(host)
            if _RATE.cancel():
                break
            try:
                if not self.csrf:
                    self._refresh_csrf()
                h = dict(kw.get("headers", {}))
                h["X-CSRF-Token"] = self.csrf or ""
                extra = {k: v for k, v in kw.items() if k != "headers"}
                r = self.s.request(method, url, headers=h, timeout=15, **extra)
                if r.status_code == 403 and r.headers.get("x-csrf-token") and r.headers["x-csrf-token"] != self.csrf:
                    self.csrf = r.headers["x-csrf-token"]
                    r = self.s.request(method, url, headers={**h, "X-CSRF-Token": self.csrf}, timeout=15, **extra)
            except requests.RequestException:
                r = None
                self.csrf = None
                time.sleep(min(6, 1.0 * attempt))
                continue
            if r.status_code == 429:
                # Rate limit: wait it out (shared by all calls to this host), then try the same call again.
                try:
                    wait = float(r.headers.get("Retry-After", 0) or 0)
                except ValueError:
                    wait = 0
                rate_waits += 1
                if rate_waits <= 6:
                    _RATE.hit(host, wait or min(60, 4 * 2 ** (rate_waits - 1)))
                    attempt -= 1
                    continue
                break
            if r.status_code >= 500:
                if attempt < retries:
                    time.sleep(min(8, 1.5 * attempt))
                    continue
            break
        if r is not None:
            self.last_status = r.status_code
            # 403 can be an endpoint permission/rate-limit response rather than
            # an expired login. Only a 401 proves the saved session is rejected.
            if r.status_code == 401:
                self.last_auth_state = "invalid"
        return r

    def me(self, retries=3):
        """Check the session and distinguish expired cookies from temporary outages.
        Network errors, 429 and 5xx are retried before the result is called 'temporary'."""
        for attempt in range(1, retries + 1):
            try:
                _RATE.wait("users.roblox.com")
                r = self.s.get("https://users.roblox.com/v1/users/authenticated", timeout=15)
                if r.status_code == 429:
                    _RATE.hit("users.roblox.com", float(r.headers.get("Retry-After", 0) or 8))
                if r.status_code == 200:
                    self.last_auth_state = "authenticated"
                    return r.json()
                if r.status_code == 401:
                    self.last_auth_state = "invalid"
                    return None
                self.last_auth_state = "temporary"
            except (requests.RequestException, ValueError):
                self.last_auth_state = "temporary"
            if attempt < retries:
                time.sleep(1.0 * attempt)
        return None

    def me_after_login(self, tries=4):
        """Right after a login the cookie can take a moment to be accepted: retry even on 401."""
        for attempt in range(tries):
            me = self.me(retries=2)
            if me:
                return me
            if attempt < tries - 1:
                time.sleep(1.5)
        return None

    def auth_ticket(self):
        r = self.req("POST", "https://auth.roblox.com/v1/authentication-ticket",
                     headers={"Referer": "https://www.roblox.com/", "Origin": "https://www.roblox.com",
                              "Content-Type": "application/json"})
        return r.headers.get("rbx-authentication-ticket") if r is not None else None

    def friends(self, user_id):
        r = self.req("GET", f"https://friends.roblox.com/v1/users/{user_id}/friends")
        if r is None or r.status_code != 200:
            return None
        try:
            data = r.json().get("data", [])
        except ValueError:
            return None
        missing = [f["id"] for f in data if not f.get("name")]
        for i in range(0, len(missing), 100):
            rr = self.req("POST", "https://users.roblox.com/v1/users",
                          json={"userIds": missing[i:i + 100], "excludeBannedUsers": False})
            if rr is not None and rr.status_code == 200:
                info = {u["id"]: u for u in rr.json().get("data", [])}
                for f in data:
                    u = info.get(f["id"])
                    if u:
                        f["name"] = u.get("name", str(f["id"]))
                        f["displayName"] = u.get("displayName", f["name"])
        for f in data:
            f.setdefault("name", str(f["id"]))
            f.setdefault("displayName", f["name"])
        return data

    def presence(self, user_ids):
        ids, out = list(user_ids), []
        for i in range(0, len(ids), 200):
            r = self.req("POST", "https://presence.roblox.com/v1/presence/users", json={"userIds": ids[i:i + 200]})
            if r is not None and r.status_code == 200:
                out.extend(r.json().get("userPresences", []))
        return out

    def resolve_user(self, text):
        """Username OR display name -> (id, name, displayName) or None"""
        text = text.strip().lstrip("@")
        if not text:
            return None
        try:
            r = self.req("POST", "https://users.roblox.com/v1/usernames/users",
                         json={"usernames": [text], "excludeBannedUsers": True})
            if r is not None and r.status_code == 200 and r.json().get("data"):
                u = r.json()["data"][0]
                return u["id"], u["name"], u.get("displayName", u["name"])
        except Exception:
            pass
        try:
            r = self.req("GET", "https://users.roblox.com/v1/users/search",
                         params={"keyword": text, "limit": 25})
            if r is not None and r.status_code == 200:
                for u in r.json().get("data", []):
                    if u.get("name", "").lower() == text.lower() or u.get("displayName", "").lower() == text.lower():
                        return u["id"], u["name"], u.get("displayName", u["name"])
        except Exception:
            pass
        return None


# --------------------------------------------------------------------------
# Microsoft Edge login.
# Edge is started normally (no automation mode). The program only types the
# username/password; any verification step is completed by you in the window.
# --------------------------------------------------------------------------
def find_edge():
    pf, pf86 = os.environ.get("ProgramFiles", ""), os.environ.get("ProgramFiles(x86)", "")
    for base in (pf86, pf):
        path = os.path.join(base, "Microsoft", "Edge", "Application", "msedge.exe")
        if base and os.path.exists(path):
            return path
    return None


class CDP:
    """Tiny Chrome DevTools client (read cookies, load pages, fill fields)."""

    def __init__(self, ws_url):
        import websocket
        self.ws = websocket.create_connection(ws_url, timeout=15, suppress_origin=True)
        self.i = 0

    def call(self, method, **params):
        self.i += 1
        self.ws.send(json.dumps({"id": self.i, "method": method, "params": params}))
        while True:
            m = json.loads(self.ws.recv())
            if m.get("id") == self.i:
                if "error" in m:
                    raise RuntimeError(m["error"].get("message", "DevTools error"))
                return m.get("result", {})

    def eval(self, expr):
        r = self.call("Runtime.evaluate", expression=expr, returnByValue=True)
        return r.get("result", {}).get("value")

    def eval_async(self, expr, timeout=15):
        try:
            self.ws.settimeout(timeout + 5)  # long page flows may take longer than the default read timeout
        except Exception:
            pass
        try:
            r = self.call("Runtime.evaluate", expression=expr, returnByValue=True, awaitPromise=True)
        finally:
            try:
                self.ws.settimeout(15)
            except Exception:
                pass
        return r.get("result", {}).get("value")

    def close(self):
        try:
            self.ws.close()
        except Exception:
            pass


def _free_port():
    with socket.socket() as sk:
        sk.bind(("127.0.0.1", 0))
        return sk.getsockname()[1]


_READY_JS = """
(function(){
  return !!(document.getElementById('login-username')
    || document.querySelector('input[name="username"]')
    || document.querySelector('input[autocomplete="username"]')
    || document.querySelector('form input[type="text"]'));
})()
"""

_FILL_JS = """
(function(u, p){
  function pick(sels){
    for(var i=0;i<sels.length;i++){
      var el = document.querySelector(sels[i]);
      if(el) return el;
    }
    return null;
  }
  var uEl = pick(['#login-username',
                  'input[name="username"]',
                  'input[autocomplete="username"]',
                  'form input[type="text"]']);
  var pEl = pick(['#login-password',
                  'input[name="password"]',
                  'input[autocomplete="current-password"]',
                  'input[type="password"]']);
  if(!uEl || !pEl) return false;
  var setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
  function fill(el, v){
    try { el.focus(); } catch(e) {}
    setter.call(el, '');
    el.dispatchEvent(new Event('input', {bubbles:true}));
    setter.call(el, v);
    el.dispatchEvent(new Event('input', {bubbles:true}));
    el.dispatchEvent(new Event('change', {bubbles:true}));
    el.dispatchEvent(new KeyboardEvent('keydown', {bubbles:true, key:'End'}));
    el.dispatchEvent(new KeyboardEvent('keyup', {bubbles:true, key:'End'}));
    try { el.blur(); } catch(e) {}
    el.dispatchEvent(new Event('blur', {bubbles:true}));
  }
  fill(uEl, u);
  if(p){ fill(pEl, p); }
  return uEl.value === u && (!p || pEl.value === p);
})(%s, %s)
"""

_SUBMIT_JS = """
(function(){
  function pick(sels){
    for(var i=0;i<sels.length;i++){
      var el = document.querySelector(sels[i]);
      if(el) return el;
    }
    return null;
  }
  var btn = pick(['#login-button',
                  'button[type="submit"]',
                  'form button']);
  var pEl = pick(['#login-password',
                  'input[name="password"]',
                  'input[type="password"]']);
  if(!btn && !pEl) return 'nobtn';
  if(btn && (btn.disabled || btn.getAttribute('aria-disabled') === 'true')) return 'disabled';
  if(btn){ try { btn.click(); } catch(e) {} }
  if(pEl){
    try {
      pEl.focus();
      pEl.dispatchEvent(new KeyboardEvent('keydown', {bubbles:true, key:'Enter', code:'Enter', keyCode:13, which:13}));
      pEl.dispatchEvent(new KeyboardEvent('keypress', {bubbles:true, key:'Enter', code:'Enter', keyCode:13, which:13}));
      pEl.dispatchEvent(new KeyboardEvent('keyup', {bubbles:true, key:'Enter', code:'Enter', keyCode:13, which:13}));
    } catch(e) {}
  }
  var form = (btn && (btn.form || btn.closest('form'))) || (pEl && pEl.closest('form'));
  if(form){
    try { form.requestSubmit ? form.requestSubmit() : form.submit(); } catch(e) {}
  }
  return 'clicked';
})()
"""


def _is_roblox_url(url):
    try:
        host = (urllib.parse.urlparse(url).hostname or "").lower()
    except ValueError:
        return False
    return host == "roblox.com" or host.endswith(".roblox.com")


class AnyEvent:
    """Looks like a threading.Event but is set when ANY of the given events (or callables returning one) is set."""

    def __init__(self, *sources):
        self.sources = sources

    def _events(self):
        for source in self.sources:
            event = source() if callable(source) else source
            if event is not None:
                yield event

    def is_set(self):
        return any(event.is_set() for event in self._events())

    def wait(self, timeout=None):
        end = None if timeout is None else time.monotonic() + timeout
        while True:
            if self.is_set():
                return True
            if end is None:
                time.sleep(0.1)
                continue
            remaining = end - time.monotonic()
            if remaining <= 0:
                return False
            time.sleep(min(0.1, remaining))


def kill_edge_tree(proc=None, sweep=True):
    """Close Edge completely (the started process tree plus, with sweep=True, any leftover window that
    uses one of the launcher's own profiles). Other Edge windows of yours stay open."""
    if proc is not None:
        try:
            subprocess.run(["taskkill", "/PID", str(proc.pid), "/T", "/F"],
                           capture_output=True, creationflags=NO_WINDOW, timeout=10)
        except Exception:
            pass
    if not sweep:
        return
    try:
        markers = [os.path.basename(EDGE_PROFILE), os.path.basename(FLEET_DIR)]
        cond = " -or ".join(f"$_.CommandLine -like '*{m}*'" for m in markers)
        ps = ("Get-CimInstance Win32_Process -Filter \"Name='msedge.exe'\" | "
              f"Where-Object {{ {cond} }} | "
              "ForEach-Object { Stop-Process -Id $_.ProcessId -Force -ErrorAction SilentlyContinue }")
        subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                       capture_output=True, creationflags=NO_WINDOW, timeout=20)
    except Exception:
        pass


def clock_skew_seconds():
    """Roblox login tickets are time based: a wrong PC clock causes authentication errors."""
    try:
        r = requests.head("https://www.roblox.com", timeout=8)
        date_header = r.headers.get("Date")
        if date_header:
            return (parsedate_to_datetime(date_header) - datetime.now(timezone.utc)).total_seconds()
    except Exception:
        pass
    return None


def _open_edge(log, cancel_event=None):
    """Start a fresh Edge (leftovers closed first). Returns (proc, cdp) or (None, None)."""
    exe = find_edge()
    if not exe:
        log("Microsoft Edge was not found. Please install Edge.")
        return None, None
    kill_edge_tree(None)
    port = _free_port()
    os.makedirs(EDGE_PROFILE, exist_ok=True)
    proc = subprocess.Popen([exe, f"--remote-debugging-port={port}", f"--user-data-dir={EDGE_PROFILE}",
                             "--no-first-run", "--no-default-browser-check", "about:blank"])
    ws_url, end = None, time.time() + 25
    while time.time() < end and not ws_url:
        if cancel_event is not None and cancel_event.is_set():
            kill_edge_tree(proc)
            return None, None
        try:
            tabs = requests.get(f"http://127.0.0.1:{port}/json", timeout=2).json()
            pages = [t for t in tabs if t.get("type") == "page" and t.get("webSocketDebuggerUrl")]
            if pages:
                ws_url = pages[0]["webSocketDebuggerUrl"]
                break
        except Exception:
            pass
        time.sleep(0.4)
    if not ws_url:
        kill_edge_tree(proc)
        return None, None
    try:
        cdp = CDP(ws_url)
        cdp.call("Network.enable")
        try:
            cdp.call("Page.enable")
        except Exception:
            pass
        warm_end = time.time() + 1.5
        while time.time() < warm_end:
            try:
                if cdp.eval("document.readyState === 'complete'"):
                    break
            except Exception:
                pass
            time.sleep(0.15)
        return proc, cdp
    except Exception:
        kill_edge_tree(proc)
        return None, None


def _edge_login_one(name, pw, log, cancel_event, force_fresh, shared=None):
    """One login in a freshly started Edge. Returns (outcome, cookie);
    outcome is ok / timeout / cancel / error (error = worth retrying with another fresh Edge)."""
    def cancelled():
        return cancel_event is not None and cancel_event.is_set()

    prof = LOGIN_PROFILES.get(LOGIN_MODE["mode"], LOGIN_PROFILES["normal"])
    force_fresh = bool(force_fresh or prof["fresh"])
    keep = {"v": False}
    if shared is not None and shared.get("cdp") is not None:
        proc, cdp = shared["proc"], shared["cdp"]
    else:
        proc, cdp = _open_edge(log, cancel_event)
    if cdp is None:
        return ("cancel" if cancelled() else "error"), None
    try:
        if not force_fresh:
            # Reuse a still-valid session already stored in the launcher's own Edge profile.
            try:
                existing = cdp.call("Network.getAllCookies").get("cookies", [])
                edge_cookie = next((c.get("value") for c in existing
                                    if c.get("name") == ".ROBLOSECURITY"
                                    and "roblox.com" in c.get("domain", "") and c.get("value")), None)
                if edge_cookie:
                    user = RobloxSession(edge_cookie).me()
                    if user and user.get("name", "").lower() == name.lower():
                        log(f"{name}: reused the saved Edge session.")
                        keep["v"] = shared is not None
                        return "ok", edge_cookie
            except Exception:
                pass
        else:
            try:
                cdp.call("Network.clearBrowserCookies")
                cdp.call("Network.clearBrowserCache")
            except Exception:
                pass
        cdp.call("Network.deleteCookies", name=".ROBLOSECURITY", domain=".roblox.com")
        ready = False
        min_ready = max(float(prof.get("ready", 15)), 30.0)
        for page_try in range(1, 4):
            if cancelled():
                return "cancel", None
            if page_try == 1:
                cdp.call("Page.navigate", url="https://www.roblox.com/login")
            else:
                time.sleep(1.2)
                cdp.call("Page.reload", ignoreCache=True)
            end = time.time() + min_ready
            doc_ready = False
            while time.time() < end:
                if cancelled():
                    return "cancel", None
                try:
                    if not doc_ready and cdp.eval("document.readyState === 'complete'"):
                        doc_ready = True
                except Exception:
                    pass
                if doc_ready and cdp.eval(_READY_JS):
                    ready = True
                    break
                time.sleep(max(float(prof["poll"]), 0.35))
            if ready:
                break
            if page_try < 3:
                log(f"{name}: login page not ready - refreshing the page ({page_try}/2) ...")
                time.sleep(1.5)
        if not ready:
            log(f"{name}: the page still does not load - restarting Edge.")
            return "error", None
        time.sleep(max(float(prof["settle"]), 1.5))
        filled = False
        for _ in range(3):
            if cdp.eval(_FILL_JS % (json.dumps(name), json.dumps(pw or ""))):
                filled = True
                break
            time.sleep(0.7)
        if not filled:
            log(f"{name}: login form did not react - refreshing the page ...")
            try:
                cdp.call("Page.reload", ignoreCache=True)
            except Exception:
                pass
            time.sleep(max(float(prof["settle"]), 1.5) + 2.5)
            for _ in range(14):
                try:
                    if cdp.eval("document.readyState === 'complete'") and cdp.eval(_READY_JS):
                        filled = bool(cdp.eval(_FILL_JS % (json.dumps(name), json.dumps(pw or ""))))
                        break
                except Exception:
                    pass
                time.sleep(max(float(prof["poll"]), 0.4) + 0.3)
        if not filled:
            log(f"{name}: the form still does not react - restarting Edge.")
            return "error", None
        if not pw:
            log(f"{name}: no password saved - please type it in the Edge window.")
        else:
            submit_end = time.time() + 8.0
            clicked = False
            while time.time() < submit_end and not cancelled():
                try:
                    verdict = cdp.eval(_SUBMIT_JS)
                except Exception:
                    verdict = None
                if verdict == "clicked":
                    clicked = True
                    break
                if verdict == "disabled":
                    try:
                        cdp.eval(_FILL_JS % (json.dumps(name), json.dumps(pw)))
                    except Exception:
                        pass
                time.sleep(0.5)
            if not clicked:
                log(f"{name}: login button stayed disabled - the form may need a manual push.")
        start, hinted, ck = time.time(), False, None
        last_peek, last_verdict = 0.0, ""
        while time.time() - start < 240 and not cancelled():
            try:
                for c in cdp.call("Network.getAllCookies").get("cookies", []):
                    if c["name"] == ".ROBLOSECURITY" and "roblox.com" in c.get("domain", "") and c.get("value"):
                        ck = c["value"]
            except Exception:
                pass
            if ck:
                break
            if time.time() - last_peek > 2.0:
                last_peek = time.time()
                try:
                    page_text = str(cdp.eval("(document.body && document.body.innerText || '').slice(0, 3000)") or "").lower()
                except Exception:
                    page_text = ""
                verdict = _login_page_problem(page_text)
                if verdict and verdict != last_verdict:
                    last_verdict = verdict
                    log(f"{name}: {verdict}")
                    if verdict.startswith("Wrong"):
                        return "badpass", None
            if not hinted and time.time() - start > 6:
                log(f"{name}: if Roblox shows a verification (e.g. press-and-hold), please complete it in Edge.")
                hinted = True
            if cancel_event is not None:
                cancel_event.wait(prof["poll"])
            else:
                time.sleep(prof["poll"])
        if cancelled():
            return "cancel", None
        if ck:
            log(f"{name}: logged in.")
            keep["v"] = shared is not None
            return "ok", ck
        log(f"{name}: login was not completed.")
        return "timeout", None
    except Exception as exc:
        log(f"{name}: browser error - {str(exc)[:100]}")
        return "error", None
    finally:
        if keep["v"]:
            shared.update(proc=proc, cdp=cdp)  # fast mode: the same Edge serves the next account
        else:
            cdp.close()
            kill_edge_tree(proc)  # restart the browser after every login
            if shared is not None:
                shared.clear()
            time.sleep(1.2)  # let Edge release the profile lock before the next start


def edge_login_many(items, log, cancel_event=None, force_fresh=False):
    """items: [(account, password)] -> {username: cookie}.
    Edge is closed and started again for every login; if the browser misbehaves the login is
    retried (up to 3 times) with a clean Edge."""
    results = {}
    if not find_edge():
        log("Microsoft Edge was not found. Please install Edge.")
        return results
    try:
        import websocket  # noqa: F401
    except ImportError:
        log("Missing Python package: run 'pip install websocket-client'.")
        return results
    shared = {} if LOGIN_PROFILES.get(LOGIN_MODE["mode"], {}).get("shared") else None
    for acc, pw in items:
        if cancel_event is not None and cancel_event.is_set():
            log("Login queue cancelled.")
            break
        name = acc["name"]
        cookie = None
        max_tries = 2
        for login_try in range(1, max_tries + 1):
            outcome, cookie = _edge_login_one(name, pw, log, cancel_event, force_fresh, shared)
            if outcome != "error":
                break
            if login_try < max_tries:
                log(f"{name}: refreshing did not help - restarting Edge and trying again ({login_try}/{max_tries}) ...")
                for _ in range(30):  # 3s cooldown, broken up so cancel stays responsive
                    if cancel_event is not None and cancel_event.is_set():
                        break
                    time.sleep(0.1)
        if outcome == "cancel":
            log(f"{name}: login cancelled.")
            break
        if cookie:
            results[name] = cookie
    if shared and shared.get("cdp") is not None:
        try:
            shared["cdp"].close()
        except Exception:
            pass
        kill_edge_tree(shared.get("proc"))
    return results


_PURCHASE_JS = """
(async function(productId, price, sellerId){
  async function post(token){
    return fetch('https://economy.roblox.com/v1/purchases/products/' + productId, {
      method: 'POST', credentials: 'include',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': token || ''},
      body: JSON.stringify({expectedCurrency: 1, expectedPrice: price, expectedSellerId: sellerId})
    });
  }
  try {
    var r = await post('');
    if (r.status === 403) { var t = r.headers.get('x-csrf-token'); if (t) r = await post(t); }
    var body = null; try { body = await r.json(); } catch (e) {}
    return JSON.stringify({status: r.status, body: body});
  } catch (e) { return JSON.stringify({status: 0, error: String(e)}); }
})(%s, %s, %s)
"""

_EXTENSION_PURCHASE_JS = """
(async function(productId, price, sellerId){
  var requestId = 'crimson-' + Date.now() + '-' + Math.random().toString(16).slice(2);
  return await new Promise(function(resolve){
    var timer = setTimeout(function(){ cleanup(); resolve(JSON.stringify({status: 0, error: 'extension timeout'})); }, 3500);
    function cleanup(){ clearTimeout(timer); window.removeEventListener('message', receive); }
    function receive(event){
      var d = event.data || {};
      if (event.source !== window || d.source !== 'CrimsonEdgeBridge' || d.requestId !== requestId) return;
      cleanup(); resolve(JSON.stringify(d));
    }
    window.addEventListener('message', receive);
    window.postMessage({source: 'CrimsonLauncher', type: 'purchase', requestId: requestId,
                        productId: productId, price: price, sellerId: sellerId}, location.origin);
  });
})(%s, %s, %s)
"""

_FETCH_JS = """
(async function(url, method, body){
  async function go(token){
    return fetch(url, {method: method, credentials: 'include',
      headers: {'Content-Type': 'application/json', 'X-CSRF-Token': token || ''},
      body: body === null ? undefined : JSON.stringify(body)});
  }
  try {
    var r = await go('');
    if (r.status === 403) { var t = r.headers.get('x-csrf-token'); if (t) r = await go(t); }
    var b = null; try { b = await r.json(); } catch (e) {}
    return JSON.stringify({status: r.status, body: b, challenge: r.headers.get('rblx-challenge-id') || null});
  } catch (e) { return JSON.stringify({status: 0, error: String(e)}); }
})(%s, %s, %s)
"""

class EdgeBuyer:
    """Buys / gets Marketplace items inside Edge. The saved Roblox cookie is injected,
    so no password or login is needed. Roblox's own purchase call is used from the
    catalog page; if that fails the on-page Get/Buy button is clicked instead."""

    def __init__(self, log, profile=None, position=None, sweep=True, background=False):
        self.log = log
        self.profile = profile or EDGE_PROFILE
        self.position = position
        self.sweep = sweep
        self.background = background
        self.proc = None
        self.cdp = None
        self.port = None
        self.main_id = None
        self.last_url = None
        self.last_ui_message = ""

    def start(self):
        exe = find_edge()
        if not exe:
            self.log("Microsoft Edge was not found.")
            return False
        try:
            import websocket  # noqa: F401
        except ImportError:
            self.log("Missing Python package: run 'pip install websocket-client'.")
            return False
        if self.sweep:
            kill_edge_tree(None)  # clean restart of the launcher's own Edge
        port = _free_port()
        self.port = port
        os.makedirs(self.profile, exist_ok=True)
        cmd = [exe, f"--remote-debugging-port={port}", f"--user-data-dir={self.profile}",
               "--no-first-run", "--no-default-browser-check", "--window-size=1100,800",
               "--disable-background-timer-throttling", "--disable-renderer-backgrounding",
               "--disable-backgrounding-occluded-windows", "--disable-gpu", "--mute-audio",
               "--disable-sync", "--disable-default-apps", "--disable-background-networking",
               "--renderer-process-limit=2", "--disk-cache-size=33554432"]
        if os.path.isfile(os.path.join(EXTENSION_DIR, "manifest.json")):
            # Chromium loads unpacked extensions only for this controlled Edge
            # process/profile; it does not modify the user's normal Edge.
            cmd.append(f"--load-extension={EXTENSION_DIR}")
            # Current Edge/Chromium builds ignore --load-extension unless this switch re-allows it.
            cmd.append("--disable-features=DisableLoadExtensionCommandLineSwitch,Translate,MediaRouter")
        if self.background:
            # Keep automated Marketplace work out of the way.  It can still be
            # restored from the taskbar if Roblox asks the user to verify.
            cmd.append("--start-minimized")
        if self.position:
            cmd.append(f"--window-position={self.position[0]},{self.position[1]}")
        self.proc = subprocess.Popen(cmd + ["about:blank"])
        ws_url, end = None, time.time() + 25
        while time.time() < end and not ws_url:
            try:
                tabs = requests.get(f"http://127.0.0.1:{port}/json", timeout=2).json()
                pages = [t for t in tabs if t.get("type") == "page" and t.get("webSocketDebuggerUrl")]
                if pages:
                    ws_url = pages[0]["webSocketDebuggerUrl"]
                    break
            except Exception:
                pass
            time.sleep(0.4)
        if not ws_url:
            self.log("Edge did not respond. Close other Edge windows opened by Multi-Launcher and try again.")
            self.close()
            return False
        try:
            self.main_id = ws_url.rstrip("/").rsplit("/", 1)[-1]
            self.cdp = CDP(ws_url)
            self.cdp.call("Network.enable")
            self.cdp.call("Page.enable")
            try:  # the click library is injected directly, so it works even when Edge refuses the add-on
                self.cdp.call("Page.addScriptToEvaluateOnNewDocument", source=_UI_LIB_JS)
            except Exception:
                pass
            return True
        except Exception as exc:
            self.log(f"Could not control Edge: {str(exc)[:100]}")
            self.close()
            return False

    def sign_in(self, cookie):
        self.cdp.call("Network.deleteCookies", name=".ROBLOSECURITY", domain=".roblox.com")
        self.cdp.call("Network.setCookie", name=".ROBLOSECURITY", value=cookie, domain=".roblox.com",
                      path="/", secure=True, httpOnly=True)

    def _open(self, url):
        self.last_url = url
        self.cdp.call("Page.navigate", url=url)
        end = time.time() + 20
        time.sleep(0.15)
        host = url.split("/")[2] if url.count("/") >= 2 else ""
        ready = "(location.hostname.indexOf(%s) >= 0 && document.readyState !== 'loading')" % json.dumps(host)
        while time.time() < end:
            try:
                if self.cdp.eval(ready):
                    break
            except Exception:
                pass
            time.sleep(0.08)
        self.guard()

    def guard(self):
        """Close tabs that left roblox.com (for example through a social link) and bring the main tab back."""
        if not self.port:
            return
        try:
            tabs = requests.get(f"http://127.0.0.1:{self.port}/json", timeout=2).json()
        except Exception:
            return
        for tab in tabs:
            if tab.get("type") != "page":
                continue
            url = tab.get("url", "") or ""
            if (_is_roblox_url(url) or url in ("", "about:blank")
                    or url.startswith(("chrome-extension://", "edge://", "chrome://", "devtools://"))):
                continue
            if tab.get("id") == self.main_id:
                try:
                    self.cdp.call("Page.navigate", url=self.last_url or "https://www.roblox.com/home")
                    self.log("The browser left roblox.com by mistake - went back.")
                except Exception:
                    pass
            else:
                try:
                    requests.get(f"http://127.0.0.1:{self.port}/json/close/{tab.get('id')}", timeout=2)
                    self.log("Closed an unwanted tab that was opened outside roblox.com.")
                except Exception:
                    pass

    def ensure_ui(self, cdp=None):
        """The Edge add-on loads the click library into every roblox.com page; inject it ourselves if it did not."""
        cdp = cdp or self.cdp
        try:
            if cdp.eval("!!window.__crimsonUI"):
                return True
            cdp.eval(_UI_LIB_JS)
            return bool(cdp.eval("!!window.__crimsonUI"))
        except Exception:
            return False

    def ui_run(self, action, timeout=25, cdp=None, **args):
        """Run one safe page flow (bio / displayName / follow / buy / confirm). -> {'ok': bool, 'code': str}"""
        cdp = cdp or self.cdp
        if not self.ensure_ui(cdp):
            return {"ok": False, "code": "nolib"}
        expr = ("window.__crimsonUI.run(%s, %s).then(function(r){return JSON.stringify(r);})"
                % (json.dumps(action), json.dumps(args)))
        try:
            raw = cdp.eval_async(expr, timeout=timeout)
            result = json.loads(raw) if raw else {"ok": False, "code": "empty"}
        except Exception as exc:
            result = {"ok": False, "code": "error", "error": str(exc)[:80]}
        self.guard()
        return result

    def _api_buy(self, item, cdp=None):
        cdp = cdp or self.cdp
        args = (json.dumps(item.get("product")), json.dumps(int(item.get("price") or 0)),
                json.dumps(item.get("creator") or 0))
        try:
            # The extension executes in Roblox's own page context.  A direct
            # page request remains a compatibility fallback if Edge blocked the
            # extension or Roblox has not injected it yet.
            raw = cdp.eval_async(_EXTENSION_PURCHASE_JS % args)
            data = json.loads(raw) if raw else {}
        except Exception:
            data = {}
        if not data.get("status"):
            try:
                raw = cdp.eval_async(_PURCHASE_JS % args)
                data = json.loads(raw) if raw else {}
            except Exception:
                return "fail"
        body = data.get("body") or {}
        if data.get("status") == 200 and (body.get("purchased") is True or body.get("reason") == "AlreadyOwned"):
            return "done"
        if body.get("reason") == "InsufficientFunds":
            return "funds"
        return "fail"

    def _click_buy(self, cdp=None):
        """Click Get/Buy on the item page, then confirm with Get Now / Buy Now (scoped, never leaves roblox.com)."""
        result = self.ui_run("buy", timeout=25, cdp=cdp)
        if result.get("ok"):
            time.sleep(0.6)
            return True
        return False

    def buy(self, item, prefer_api=True):
        """Get an approved Marketplace item through Roblox's own page API first.

        The fleet is already signed in on roblox.com, so a direct request avoids
        loading an entire catalog page for every item.  A normal page/button
        interaction remains the compatibility fallback when Roblox rejects the
        request or requires a visual verification.
        """
        if item.get("kind") == "bundle" and item.get("bundle"):
            url = f"https://www.roblox.com/bundles/{item['bundle']}"
        elif item.get("asset_id"):
            url = f"https://www.roblox.com/catalog/{item['asset_id']}"
        else:
            return False
        result = self._api_buy(item)
        if result == "done":
            return True
        if result == "funds":
            self.log(f"Not enough Robux for '{item.get('name')}'.")
            return False
        # API fallbacks still use the official catalog UI, where Roblox can
        # present a challenge or any changed purchase flow.
        self._open(url)
        if self._click_buy():
            return True
        return self._api_buy(item) == "done"

    @staticmethod
    def item_url(item):
        if item.get("kind") == "bundle" and item.get("bundle"):
            return f"https://www.roblox.com/bundles/{item['bundle']}"
        if item.get("asset_id"):
            return f"https://www.roblox.com/catalog/{item['asset_id']}"
        return None

    def _tab_buy(self, item, cancelled):
        """One tab for one item: open its page, buy through the page (API call first, then the safe button click)."""
        url = self.item_url(item)
        if not url or cancelled():
            return False
        tab_id, tab = None, None
        try:
            info = requests.put(f"http://127.0.0.1:{self.port}/json/new?{url}", timeout=8).json()
            tab_id = info.get("id")
            tab = CDP(info["webSocketDebuggerUrl"])
            end = time.time() + 25
            while time.time() < end and not cancelled():
                try:
                    if tab.eval("document.readyState") == "complete":
                        break
                except Exception:
                    pass
                time.sleep(0.25)
            time.sleep(0.4)
            if cancelled():
                return False
            result = self._api_buy(item, cdp=tab)
            if result == "done":
                return True
            if result == "funds":
                self.log(f"Not enough Robux for '{item.get('name')}'.")
                return False
            if self._click_buy(cdp=tab):
                return True
            return self._api_buy(item, cdp=tab) == "done"
        except Exception as exc:
            self.log(f"Browser tab for '{item.get('name')}' failed ({str(exc)[:70]}).")
            return False
        finally:
            if tab is not None:
                tab.close()
            if tab_id:
                try:
                    requests.get(f"http://127.0.0.1:{self.port}/json/close/{tab_id}", timeout=3)
                except Exception:
                    pass

    def buy_many(self, items, cancelled=lambda: False, workers=8):
        """Open every item page at once (one tab each, loading in parallel) and get them all in this one window."""
        items = [i for i in items if self.item_url(i)]
        if not items:
            return {}
        with ThreadPoolExecutor(max_workers=max(1, min(workers, len(items)))) as ex:
            outcomes = list(ex.map(lambda it: self._tab_buy(it, cancelled), items))
        self.guard()
        return {id(it): ok for it, ok in zip(items, outcomes)}

    def bridge_ready(self, timeout=5):
        """True when the Crimson Edge add-on is active on the current roblox.com page."""
        end = time.time() + timeout
        while time.time() < end:
            try:
                if self.cdp.eval("!!document.getElementById('crimson-page-bridge')"):
                    return True
            except Exception:
                pass
            time.sleep(0.4)
        return False

    # ----- generic page helpers (used for bio / display name / follow / equip) -----
    goto = _open

    def api(self, url, method="GET", body=None):
        """Call a Roblox API from inside the page. -> (status, body, challenge_flag)."""
        try:
            raw = self.cdp.eval_async(_FETCH_JS % (json.dumps(url), json.dumps(method), json.dumps(body)))
            data = json.loads(raw) if raw else {}
        except Exception:
            return 0, None, False
        body_out = data.get("body")
        challenge = bool(data.get("challenge")) or "challenge" in json.dumps(body_out).lower()
        return data.get("status", 0), body_out, challenge

    def confirm_pass(self):
        """Confirm a dialog that is open right now (for example after a verification)."""
        return self.ui_run("confirm", timeout=8).get("ok")

    def ui_bio(self, text, user_id=None):
        """Own profile -> Edit Profile -> About -> text -> Save. Falls back to the settings page."""
        pages = []
        if user_id:
            pages.append(f"https://www.roblox.com/users/{user_id}/profile")
        pages.append("https://www.roblox.com/my/account#!/info")
        code = "failed"
        for url in pages:
            self._open(url)
            result = self.ui_run("bio", timeout=30, text=text)
            if result.get("ok"):
                return "saved"
            code = result.get("code", "failed")
            self.last_ui_message = result.get("message", "")
            if code == "limit":
                break
        return code

    def ui_display_name(self, new):
        self._open("https://www.roblox.com/my/account#!/info")
        result = self.ui_run("displayName", timeout=30, name=new)
        self.last_ui_message = result.get("message", "")
        return "saved" if result.get("ok") else result.get("code", "failed")

    def ui_follow(self, user_id):
        self._open(f"https://www.roblox.com/users/{user_id}/profile")
        result = self.ui_run("follow", timeout=25)
        return "followed" if result.get("ok") else result.get("code", "failed")

    def close(self):
        if self.cdp:
            self.cdp.close()
            self.cdp = None
        if self.proc:
            kill_edge_tree(self.proc, sweep=self.sweep)
            self.proc = None


class BrowserFleet:
    """One minimized, signed-in Edge window per account - but never more than a few at the same time
    (RAM).  Windows start in the background as soon as a tool starts and are closed again right after
    their account is finished, so the next account can use the free slot."""

    def __init__(self, app):
        self.app = app
        self.items = {}
        self.lock = threading.Lock()
        self.futures = {}
        self.abandoned = set()
        self.closed = False
        self._pool = None
        self.cap = 3 if app.extreme_save_mode.get() else 4
        self._slots = threading.BoundedSemaphore(self.cap)
        self._index = 0

    def _acquire(self):
        while not self._slots.acquire(timeout=0.4):
            if self.closed or self.app._cancelled():
                return False
        return True

    def _open_one(self, acc, sess):
        name = acc["name"]
        if self.closed or name in self.abandoned or not self._acquire():
            return None
        browser = None
        try:
            if self.closed or name in self.abandoned:
                return None
            with self.lock:
                index = self._index
                self._index += 1
            safe = "".join(ch if ch.isalnum() else "_" for ch in name)
            browser = EdgeBuyer(self.app.log, profile=os.path.join(FLEET_DIR, safe),
                                position=(40 * (index % 6), 40 * (index % 6)), sweep=False, background=True)
            if not browser.start():
                browser = None
                return None
            cookie = self.app._cookie_of(acc, sess)
            if not cookie:
                self.app.log(f"{name}: no saved login cookie for the browser.")
                return None
            browser.sign_in(cookie)  # signed in before the first page loads - no extra start page
            with self.lock:
                if self.closed or name in self.abandoned:
                    return None
                self.items[name] = browser
            keep, browser = browser, None
            return keep
        except Exception as exc:
            self.app.log(f"{name}: could not open the browser ({str(exc)[:80]}).")
            return None
        finally:
            if browser is not None:
                try:
                    browser.sweep = False
                    browser.close()
                except Exception:
                    pass
            with self.lock:
                kept = name in self.items
            if not kept:
                self._slots.release()

    def prestart(self, pairs):
        """Start the windows in the background, right when a tool starts."""
        pairs = list(pairs)
        if not pairs or self.app._cancelled() or self.futures:
            return
        kill_edge_tree(None)  # one clean restart of the launcher's own Edge windows
        self._pool = ThreadPoolExecutor(max_workers=len(pairs))
        for acc, sess in pairs:
            self.futures[acc["name"]] = self._pool.submit(self._open_one, acc, sess)

    open = prestart  # same thing: starting is never blocking, get() waits for the window

    def get(self, acc):
        name = acc["name"]
        with self.lock:
            browser = self.items.get(name)
        if browser is not None:
            return browser
        future = self.futures.get(name)
        if future is None:
            return None
        end = time.time() + 240
        while not future.done():
            if self.closed or self.app._cancelled() or time.time() > end:
                return None
            time.sleep(0.15)
        try:
            return future.result()
        except Exception:
            return None

    def for_account(self, acc, sess):
        """Window of this account (opened on demand if it was not started before)."""
        browser = self.get(acc)
        if browser is not None:
            return browser
        self.abandoned.discard(acc["name"])
        self.futures.pop(acc["name"], None)
        return self._open_one(acc, sess)

    def release(self, acc):
        """This account is finished (or never needed the browser): close its window and free the slot."""
        name = acc["name"]
        self.abandoned.add(name)
        future = self.futures.pop(name, None)
        if future is not None:
            future.cancel()
        with self.lock:
            browser = self.items.pop(name, None)
        if browser is not None:
            try:
                browser.sweep = False
                browser.close()
            except Exception:
                pass
            self._slots.release()
            self.abandoned.discard(name)

    def close(self):
        self.closed = True
        for future in list(self.futures.values()):
            future.cancel()
        self.futures = {}
        with self.lock:
            browsers = list(self.items.values())
            self.items = {}
        for browser in browsers:
            try:
                browser.sweep = False
                browser.close()
            except Exception:
                pass
        if self._pool is not None:
            self._pool.shutdown(wait=False)
        if browsers:
            kill_edge_tree(None)


def build_uri(ticket, place_id=None, game_id=None, variant=0):
    """variant 0 = normal; 1 = without LaunchExp; 2 = minimal (no LaunchExp, no locale).
    Different start methods are tried when the client keeps closing with an authentication error."""
    now = int(time.time() * 1000)
    tracker = str(uuid.uuid4().int)[:11]
    tail = "" if variant >= 2 else "+robloxLocale:en_us+gameLocale:en_us"
    tail += "+channel:" + ("+LaunchExp:InApp" if variant == 0 else "")
    if place_id is None:
        return f"roblox-player:1+launchmode:app+gameinfo:{ticket}+launchtime:{now}{tail}"
    url = ("https://assetgame.roblox.com/game/PlaceLauncher.ashx?request=RequestGameJob"
           f"&browserTrackerId={tracker}&placeId={place_id}"
           + (f"&gameId={game_id}" if game_id else "")
           + "&isPlayTogetherGame=false")
    return (f"roblox-player:1+launchmode:play+gameinfo:{ticket}+launchtime:{now}"
            f"+placelauncherurl:{urllib.parse.quote(url, safe='')}+browsertrackerid:{tracker}{tail}")


# --------------------------------------------------------------------------
# Storage
# --------------------------------------------------------------------------
def load_accounts():
    for path in (DATA_FILE, DATA_FILE + ".bak"):
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    return data
            except Exception:
                pass
    return []


def save_accounts(accs):
    tmp = DATA_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(accs, f, indent=2)
    if os.path.exists(DATA_FILE):
        try:
            shutil.copy2(DATA_FILE, DATA_FILE + ".bak")
        except OSError:
            pass
    os.replace(tmp, DATA_FILE)


# --------------------------------------------------------------------------
# Launcher preferences
# --------------------------------------------------------------------------
DEFAULT_SETTINGS = {
    "performance_mode": True,
    "extreme_save_mode": True,
    # Recovery must be intentional: a client that you close should stay closed.
    "auto_recovery": False,
    "lean_clients": True,
    "fps_cap": 30,
    "launch_speed": "fast",
    "perf_off": [],
    "mute_clients": False,
    "auto_tile": False,
    "tiny_windows": False,
    "recent_games": [],
    "auto_fix": True,
    "login_mode": "safe",
    "flag_packs": [],
    "relaunch_on": [],
    "always_on_top": False,
    "specific_users": [],
    "version": 4,
}


def load_settings():
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            saved = json.load(f)
        if not isinstance(saved, dict):
            return dict(DEFAULT_SETTINGS)
        # Older releases defaulted Performance Mode off. Upgrade it to on once;
        # after this version the user's explicit checkbox choice is preserved.
        upgraded = int(saved.get("version", 0) or 0) < 2
        specific_users = saved.get("specific_users", [])
        if not isinstance(specific_users, list):
            specific_users = []
        return {
            "performance_mode": True if upgraded else bool(saved.get("performance_mode", True)),
            "extreme_save_mode": True if upgraded else bool(saved.get("extreme_save_mode", True)),
            "auto_recovery": bool(saved.get("auto_recovery", False)),
            "lean_clients": bool(saved.get("lean_clients", True)),
            "fps_cap": saved.get("fps_cap", 30) if saved.get("fps_cap", 30) in (0, 15, 30, 60) else 30,
            "launch_speed": saved.get("launch_speed", "fast") if saved.get("launch_speed", "fast") in ("smart", "slow", "safe", "fast", "instant") else "fast",
            "perf_off": [n for n in saved.get("perf_off", []) if isinstance(n, str)] if isinstance(saved.get("perf_off", []), list) else [],
            "mute_clients": bool(saved.get("mute_clients", False)),
            "auto_tile": bool(saved.get("auto_tile", False)),
            "tiny_windows": bool(saved.get("tiny_windows", False)),
            "auto_fix": bool(saved.get("auto_fix", True)),
            "recent_games": [g for g in saved.get("recent_games", []) if isinstance(g, dict) and str(g.get("id", "")).isdigit()][:8] if isinstance(saved.get("recent_games", []), list) else [],
            "login_mode": saved.get("login_mode") if saved.get("login_mode") in ("smart", "slow", "safe", "normal", "fast") else "safe",
            "flag_packs": [n for n in saved.get("flag_packs", []) if n in FLAG_PACKS] if isinstance(saved.get("flag_packs", []), list) else [],
            "relaunch_on": [n for n in saved.get("relaunch_on", []) if isinstance(n, str)] if isinstance(saved.get("relaunch_on", []), list) else [],
            "always_on_top": bool(saved.get("always_on_top", False)),
            "specific_users": [u for u in specific_users if isinstance(u, dict) and u.get("id") and u.get("name")],
            "version": 4,
        }
    except (OSError, ValueError, TypeError):
        return dict(DEFAULT_SETTINGS)


def save_settings(settings):
    specific_users = settings.get("specific_users", [])
    if not isinstance(specific_users, list):
        specific_users = []
    values = {
        "performance_mode": bool(settings.get("performance_mode", True)),
        "extreme_save_mode": bool(settings.get("extreme_save_mode", True)),
        "auto_recovery": bool(settings.get("auto_recovery", False)),
        "lean_clients": bool(settings.get("lean_clients", True)),
        "fps_cap": settings.get("fps_cap", 30) if settings.get("fps_cap", 30) in (0, 15, 30, 60) else 30,
        "launch_speed": settings.get("launch_speed", "fast") if settings.get("launch_speed", "fast") in ("smart", "slow", "safe", "fast", "instant") else "fast",
        "perf_off": [n for n in settings.get("perf_off", []) if isinstance(n, str)] if isinstance(settings.get("perf_off", []), list) else [],
        "mute_clients": bool(settings.get("mute_clients", False)),
        "auto_tile": bool(settings.get("auto_tile", False)),
        "tiny_windows": bool(settings.get("tiny_windows", False)),
        "auto_fix": bool(settings.get("auto_fix", True)),
        "recent_games": [g for g in settings.get("recent_games", []) if isinstance(g, dict) and str(g.get("id", "")).isdigit()][:8] if isinstance(settings.get("recent_games", []), list) else [],
        "login_mode": settings.get("login_mode") if settings.get("login_mode") in ("smart", "slow", "safe", "normal", "fast") else "safe",
        "flag_packs": [n for n in settings.get("flag_packs", []) if n in FLAG_PACKS] if isinstance(settings.get("flag_packs", []), list) else [],
        "relaunch_on": [n for n in settings.get("relaunch_on", []) if isinstance(n, str)] if isinstance(settings.get("relaunch_on", []), list) else [],
        "always_on_top": bool(settings.get("always_on_top", False)),
        "specific_users": [u for u in specific_users if isinstance(u, dict) and u.get("id") and u.get("name")],
        "version": 4,
    }
    tmp = SETTINGS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(values, f, indent=2)
    os.replace(tmp, SETTINGS_FILE)



# --------------------------------------------------------------------------
# REDSHIFT design system: palette, fonts, animation helpers and custom widgets
# --------------------------------------------------------------------------
from tkinter import font as tkfont

BG = "#000000"
SURFACE = "#0a0a0a"
SURFACE2 = "#121212"
SURFACE3 = "#1c1c1c"
INPUT = "#050505"
BORDER = "#2a2a2a"
FG = "#ffffff"
MUTED = "#a3a3a3"
DIM = "#666666"
ACCENT = "#ffffff"
ACCENT2 = "#d4d4d4"
ACCENT_DARK = "#3a3a3a"
ACCENT_LIGHT = "#ffffff"
ACCENT_SOFT = "#1a1a1a"
GREEN = "#4ade80"
AMBER = "#fbbf24"
DANGER = "#f87171"
BLUE = "#7dd3fc"
VIOLET = "#a78bfa"
# names kept for older code paths
PANEL, FIELD = SURFACE, SURFACE2
RED, RED_DARK, RED_LIGHT, RED_ROW = ACCENT, ACCENT_DARK, ACCENT_LIGHT, ACCENT_SOFT

FONT = ("Segoe UI", 10)
FONT_SMALL = ("Segoe UI", 9)
FONT_SMALL_B = ("Segoe UI", 9, "bold")
FONT_BOLD = ("Segoe UI", 10, "bold")
FONT_BIG = ("Bahnschrift SemiBold", 13)
FONT_H2 = ("Bahnschrift SemiBold", 13)
FONT_TITLE = ("Bahnschrift SemiBold", 22)
FONT_NUM = ("Bahnschrift SemiBold", 24)
FONT_MONO = ("Consolas", 9)
BOX_ON, BOX_OFF = "☒", "☐"
_MISSING = object()

_ICON_PNG_B64 = "iVBORw0KGgoAAAANSUhEUgAAAEAAAABACAIAAAAlC+aJAAAP/klEQVR42u1aaXBVRb7/d5/tXpKbFUIIWbgQkUwWEigMJQUo8MSMoCAKGHFhCeAjMChiyVbzhojbGBhqwA++iAqiTmAoFcgHBrSKgRBCCKEIYYSESWIghpAQs92z9On/+9DJ8RoCbwZFmSq6blXO6dPL7792968DcLfcLXfL3fJrFuk2jUsplSQJEQkhsiwTQhDxP0MlAnqv9ZTSn3068nOORYgkSYwxABg+fPizzz6blpYmUXq2ouLjjz8uLCwEAEmWuW3fcdYQfiKevV7v1q3vdnZ0ol9hjH344YdDhw7tclxJupPCqBtNeHj4+j+sb2xsFKDLysq2bt26efPmY8eOiZrm5uacnJywsLA7RQxJkgghAKBpWnZ29sWLFwXQioqK+fPna6rq2GfmzJknT54UXysrK7OysgT62xQY/1KkOhPPmjWrtLRUgKuurl6xYkVgYKAjIaVUCKmq6uLFiy9cuCBaHj169OGMjB6K+KWTzKRJkw4dOiQANTY25uTk9OvXT3wSqVOSJJemiVdRHxISsnbt2u+++0702r17d1pamn+XXyhS09LSdu3aJUB0dHRs2bJl0KBBPaADQH5+/pG/H3G5NGExR/Lo6OiNGze2tbUhomEYf97y57i4uNtrDbl7bu8g79at7/p8PkS0bfvjHTtSUlJ6qFDImZubKyTM/8tfnK/+WkhISNi2bRtjTBhw3bp1oaGhtyW+BaywsLD/+f3vGxuvClj79u0bM2aMaKAoiizLQnli7mfmPIOIuk/3dfoQcd3atY52JUmSZVlRFNE3/b779vz1r2LMqsqqRYsWqaoqfPXngS7Q//cLL1RVVYlpioqKpk2bdpMgiYuLa2lpsSzLNE3LsgzDYIyNHj36JhP99rcZhw8fFuOXlJTMnDnTUdxPzjaEfPThR2LoU6fKpkyZ4t8gICAgOjo6NTV1woQJs2fPGhQXBwB79uxBRF3XGWOMMcMwEPFkyUkAiImJeeqp2RMnTkxLS4uJiXHylZMVjh8/LuZ67733/pUkezMRZVlmjM2ZM2fHjh0AsHbt2ry8vNGjRycnJ0dHR3s8QW63y7Ztxlh7W3vL9y3Nzc3v5+XFx8cfLSw0TRMQJUkCQmxmI6CmaZmZmQcOHFj+u+UhoSFBQUEBfQJkRRaitrS01NXVVZyrKDlRMm3atD9t2kQlKSsrKy8vT8C4lV2NqqqSJBXsLzBN86233gKAwsLC3Nzc+fPnP/TQQykpKRER/UJCgnsoad++fYio+3xCkbZtI6Jpmpzz8vLyH6+DNDg4eLDXm56ePn369CVLluTm5p44cSI4OOjF5cstyzry9yMiWv691NQDUHl5OSLOnTs3Ly/vlVdeoZTGxsaMGzdu7NixixctBgC32+12uwMDAyVJuvfeew3dsCwLEd99990RI0YkJSXl5ORYFjNNExH/a9IkSZI8Ho/b7dY01clITpk7d27+rvxxY8ciYl1d3U2A9X4eEBv3/v37Z2RkPPHEE/PmzYuKiqqoqLAsa8iQIQX793uCgh544EHDMFpbW2u/rW1ubqaUiGg3DCNrQdbkhydTSrdt27Zo0aL6+vorV658/fXXiDhp0iSR9b/88ktJkjjniEAIFTpWFMXl0jhHWZYzMzPD+/ZFRJfLlZSYGB9/T2hoSEtLS0dHx/9jB2GpyQ89VFxc/Pbbb2dlZY0fPz5qwACXSwOAKVOmvPnGmwAgUersJjwej8cTGBQU5Ha7AUAszJzzUaNGUUqd9Dpw4MDW1lZE/Me5fyiKQil1uVyqqmrqD6WP2w0Azz333LJlywDA4/HExsZOnTp15cqVW7duLSoqevzxx69fIn5kQeG1L61YsXr16nPnzg32evtFRAx++OH8/PyAAKmp6Wp4eDilNCg4mHMu9vSIXNhN1/WgoKDExERRzxgjhIghAcC2bUBAjl6v1+sddP78BX9dkm7rA8CAyAEX/3lRkiRFUZqamvbt3bt3714AGD06PTd34969exljBMA5T/TiVdeuXbt2rTk9PV3V1MoLFwoK9suyTAitrf1W1dTAwEDTNDm3OeeIHED4DyBiTHRM3759LdMihDz//PO2bVsWs23btu2nMzM9QR7d0FVN9Xq9Aq2DA8UPEQAiIvtXV1dLEuWcK4ocEhoSHh7m8XgaGhqampqEjm9oAUop5/zs2Ypx48Zv2rTJ5XIBgKLIlEqyLDU1NVmWFRERUVtbq2kaIeiXhQkA9O0bLkkStzmz2NKlSzs6Ot5//33G2IwZM17bsIExRgkFgIiI/tdncELAtm1NUwMDAi5duqSqWreFEQDb29szMjLq6uosxnpkVdrDhQDg2LHCpKQkSmlAQICmaZRSQKRU0nW9ubk5NjbWNE1CyI8tDwDgcrsBAAGBAOd81apVZ86cqThbkZubqyoq6cYsouV6ESzLioyMtG376tWril92opQgYlpa2okTJwTKHynd/4VzDgAlJSWhoaHBwcFiBUU/RV+qqxPbRkr90RPLMgHANE0AIKIO0TAMTdPcbrdpmJxzR1Bd17vnIj2yX2xsXHNzs2EYxC9jco6qqgwePPhYYaED8oYWoJS2tLS0trYmJCT4fL6unRAC55wAVF2sioyMdLRHAACIYegdHZ0A8H1LCyISShAAgMiyzDm3uS3JEqEEsGtv09zUJMSwGaPdsSz+Rg8c6OR+0h1ehmHExcVRSs9fuEAI4TexgLNYlJeXjxo1yrZtSikQQEDOuaKq1dU1Yl1E5EICn89nGObKl1eOHzfuQmWlz+eTJMnJEQQIIUS8IqCIgcqqquTk5Ndff53ZtmVZoomQIyQsrLKqilIqDI8AlFLd5xs+PLWmpoZzfv02u6cAwkBFRUWJiYldisEuXauq0tDQYJpmYGAgtzkQ0HXdsqx1a9e+/ce3E5OS2traGhsbCSHYDbkr0XR7iiRLHR0dNdXV98THr1q1asuWLVSSbJsJPxErzLe1taqqOn4iVJ6amioC4Ho+pqcAokVZWVlwcEjfvn0ty+zugZRKHR3tjY2NnsBAjpwANU1r2bJl63NyOOfDhw8nhFRWVv4wDQHOuQMFORJC6urqfLo+YuRIzvmSJUtycnIYs0X2c7m09vb2rgjuBso5d7lcXq+3uLj4+gDoXQBJktrb269cuSLCwC9eCWN2fX19n4AA2+aia3x8POecUpqWmoaIp06dAgDkHAggoqIoiqogRwDgyAGgoqKCEDJy5EgBesiQIQ7QgIDAq1evdnZ2UomKZYEQMAwjNjbWsqzq6upe+ckb7rZLS08OGzaMMZsQ6uQbSkj9d/WapgGiEMuyLEqpbdv3DL1HURSRKAghtm3LslxUVFRQUCArsm3bYljBESUkJAAipZR31RPOudvtbmxstG3bL0FTXdcTEhK++eYbodletp7XVwkpi4uLBwwYIOJJrJgcUVaUmuoaXdcVVRFeq2kaAFimGRISkpSUdKyoyLZtSZYJENu2FyxYkJmZ2draKlGJAAGAw4cPR0ZGRkdHm5YFAIqqOmaXJHrxYpUsy46aCQHO+eDBg0tKSnoNgN4FEH5WWVlp23ZISAhjjBAn3UFnZ2dNdbVhmD6fzzm/25zbtj1x4sT6+vqamlpKqaIq69f/4dy5c5ZlLV26VJIlSZLa2tpOnz79wPgHCCHMsgBAVRRhRgBo+K6htbWNAAAgIYRSwjn2cbvdbtfp06d7DYAbuhCl1DCMy5cvR0dH67pumqZpGrbNAFBRZEVVsXtPIswqEpxgVoqLjxNCTp06tX59zvTp0xcuzNq+ffvevXslWTp9+rSu616vVyRrRJTF0R4RAKhEFUURZyDGmGmYhq73i4hob++4cuXKjQj63gVARCBw8ODBqAEDXC5XVNSA8LBwTXNJksyYLQ7p/iuox+PJy8tbvXo1ABQeLQSArAULAODRRx+dMeMJAHhh8WJd18vKygBg0582vfnGG30CAhyrIgBjzDRNxpgkS6qq9unjHhAVRQjxegcdPPi3W6dSXC5XQUFBa2vryBEjrj8xA8Bnn36GiC+++KLTZezYsRs2bBB9KysrOzs7+/fvDwDZ2dmzZs1yjJaZmWlZ1vGi470etaKiohoaGo4ePRIeFnaL9IRDqJw9exYRk5OTnaOMw9JRSt9773+ffvppf0ZN1FNKx44da9scEefMmSMYUgHd4bYmTpiwKz9fUWSHP3WEiYiIMAzjauNVTdMcJLd481FaWso5T05OIoSI0f3TmScwsJdTkiwDwNYtW0So7N+37/o24rVPnz49agTWiIiIzs7Ob2trRYObCHDDdQB//DRw4EBEFPSgSOqRkZGhoaFt7e09EpxoEBgY+Ni0aSIiH5wwwesdJNa7Hrmus7PT4/GIDaIYVkwR2T/S5XIxxpwF5NZvLnbu3ImIBw8edNQwd+7zgqVjjB0+fDg1NVWwiwKfUP/s2bMR0dAN3acj4po1a5xPhBDBKw4aNOiLL74Qm/bLly+vXLnSmWLnzp2c8wMHDvwkjlEIcP/993d5wv79iYmJq1etQsQ9e/ZkZmYuXLSorKzMNM3k5CSni+glmAjDMAQjVFlZ6XJpThgAQL9+/RoaGmpra3+3fPns2bM/+OADwcYNGzbsk08+ETM+9thjP5XoFdLPmzevo6MDEQWz8Oqrr/q3OXjwYE11zZNPPhkfH9/F16an27ZtWZZlWQ61+NRTT4mvMTEx06dPP3r06Pnz5384nQHMfHImIra1tgnbrlq16ueheMUQib/5TX5+vlBMeXn50qVLxdyEkPj4+EOHDl26dAkR897P0zRt967dPbhRznlpaammaRte2yDI9CNHjoy5/37Hbs8/91zJiRNO0N83atTPRlD7G/GRRx4pKSkR0xQXF/tz1KqqPvvMs5ZllZSUtLW12bbNLNb1Y8xmtmVagrh96aWXAgICnI4PPvjgV199JcY8c+bMEzNm3JYrAocoVhUlOzu7trZWTFlQUODcEgDA6PTRnHPGmGVajHWhZ4wxyxLUoiCnRElJSfn000/FOJcvX16xYoWw6m28+XO0Etm/f25urggMZrGPPvooISFBfFqzZo2//wj4uq4j4vbt27vCIDp606ZN7e3tIlNt3rx54MCBv9Ddq/8d0fCUlN3dN2Xft3y/cePG6OhoRVEaGxs555ZldhmhO5qHDBkcEhKybt26+vp60evzzz8f0b1Jue2XfNfz7+I5IyOjsLBQAKqvr3/55ZeLjhUhomkYIgYs00TEmuqa5cuXO9esxcXFU6dO/RWuWXsNDEmSFi5c6NxB6T5dqNzPiSxf941BbU1Ndna2qqi/5kV3r4ERFhb22muvXbt2DREty9J13TRM0zDFiQIR29vb33nnHbE5vXP/Y2Lo0KE7duwQ9LV/2bNnj9jS/tLufmvxPWbMmG3btpWVlZ05c+azzz6bPHnyr+zut/ZvFP474TvC3f8tj3Kcyv/5P6/c6Q5zt9wtd8uvXP4Prnc51nfKT0EAAAAASUVORK5CYII="
_LOGO_PNG_B64 = "iVBORw0KGgoAAAANSUhEUgAAADgAAAA4CAIAAAAn5KxJAAANZUlEQVR42u1Za3BUVbZe+zz6nYSk84Y8IIkaKhEHioRnEBUjxeUHhMgNzC0wiMooRctcyNxRmCiByUXwwq3SwgiWFmXBmDKSqRHUEkGiDDKAnUAIDiEhk6TpPLpD6E7nPPeaHzs50zc8nKtBb9Vl/zp9eu+9vr32962z9toA99q9dq+NSuNHcS6O43ieR0RCiCAIAICI/7eWSwjh+Vusmed5QsjomBgViJqmAUBGRsYzz6yeMWMmz/Nnzpypqqq6cOECAAiCoOv6z+ldw4vx8fFbt24NBAIY1hRF2blzZ1JS0ojOPzVEtqc2m83lcnV2diKiLMtvvPHG/Pnz582bt3379sCNACJ6vd5169ZZLBZGYo7jfiKIhjECsHz58sbGRua/9957LycnJ7xnZmbmnj17kFJErK+vX7x4sbHIuwuXiZo9P1H4RN2JEwxibW3t9OnT2XtRFEc8TJ48ubq6mvU8cuRIfn4+ey8Iwmjp7Nainjp16qFDh5jhL7/8srCw0PCTyWQCgPXr11dWVjKsxqhHHnnk6NEv2Kh33nknMzNz9OEaxjIzM6uqqpgxt9u9dOnScDKwbkuWLGEd1q5dy3CE87Jo8eKzZ88ioiLLW7dujYuLGzWdMRtxcXEVFRWhgRAiXr16dc2aNTabjeEwmUwGlOzs7GAwqKqqJEmU0jlz5hiMNJlMjAxms3n100+3trYiYnd397p166w2q2HoR6H81ZpfeTweRPT7/Rs3bmT6vdnrPM+fPHkSEWVJUmSZUnqluTkiIuKWCASed7lcPp8PEb/77rvly5d/L1Zyhx3Xdf3X63+9Y+cOACgvL3+7qqqruzs9PT0lJSU6OjomJmbMmDGRkZGaplVUVKwqLX17715JkhjnKKVWq3XLli2bN29+5ZVyQRBv3LjR19fn8/X6fP6Ojo7W1lanM6a0dNW2bdsIIRv+fcOOnTuY0X8WKCGELS42NvZS0yXRJD766KPJyckLFizgOG5gYKCnpycQCFy/fr2rq8vv93d0dPj9/sbGxpSUFI7jDHGoqjo4OJid/YAomtJSU8dER8fFxcXFxTmdzqioKLPZrGnaiRMn6t3uL44dM5vNDzzwgMfjAYDbYR2J0njOzc1FxIMHDuTl5X300Ufp6emJiYlJSUk5OTlmszl81PLlyxGRUuq95t3+n9tfffXVK1euMFW99Nvf3tKQxWKJj48/ePDg3LkPV1RUIOLs2bNGsO57sidBEPLy8ubOnfvkk0+mpKRcbWsrLCzcv3+/LMtz5sxJTk6KihoTCoVCoZDFYhFFUVXVyt9XZmZldnV1Fcwu+MMHfzh27NjBAwcWLlzodDpjYmL27dsriqLZbGbiE0WB5wVCSH9/fyAQ2Lz5d4IgpKamWixW1qGnp4dSeifpEELuu+++P9b+sbKy8oUXXviXBQvS09MFQcjPy6uoqCAEbDbrsD/MERGOqKgojuNiY2N7enoQ8fXXX2euYoJzuVyIKElSdnY2AFitVpPJZDYNNZvNRgh57rnniouLLRZLVlbWokWL/uM3v9m9+79ra2tzc3MNBg65LxyopmnPPvvsoUMfnairSxmXEp8QHxHhAACf3x8ZGSmKJkEQo6JEAIJIEZHjOEppbk5ubGwsALAcymi6prF4NGXKlKamJo4jjHsEAIElq+h0Ot1ut6aqHo+n+fJlll8VL1nicrlWrVoVDnQkFXp7egPBYFTUmOv9fXV1de3tHXa7vburi1IaEx2tqiqllFId8R9CzMjMYChLSkrGjRsnSZIkSREREc888yyTBfsOIQ5BRAACQCnlOC4yMvLatWtmi0U0iWOio2NjY02i2Ovz+f3+kYQ0nhApAPzlzF8ef/zx6upqu91OCOF5juP4/kAgGAwmJCb29PaKom1EYhnrjGUaHzduXF1dXVVVlaIoK1asyMnNGRwctFqtzN8jNKuqWnR0NCGk19crigJSREBCiKKq+fn5brf7tkApRQD49ttvS0pKHA4Hz/MACAiEEEppd3d3Ssq4+vp6Qji2JI4jLEoQjgwxR9XS09O3bdtmhCe2d4z9hBAgBNheEKLr+tjk5EAgEBoIRUdHM98jIs/zaWmpNTU1AIBhkuLCPIocx/l8vlBoMD09fXBwkG0uy8zb2/+WlJRsxC9CCKXY19eHiAPBIACwJamqKsuyLMmqonKEY2Ts7+9HxIGBARI2HACSx47t6urCYRoRQlRVSU5OFgTxypUrhBAatnfczd/M5suXJ02apCgKx3EIQKkuikJbW5vNaiWEsLMbpTQQCMx7bF5GxoTm5ma2mwjAcZzAC4IohOugtbU1OTlp8eLFkiwDohGqY2Ji2traOI5DRAQghAwOShMnZns8Hl3XR2Qq/wMoi15nz52dOHGisW5EMIkm7zWvrusWixkQKdWDweCCBQs+Pvzx5F9MvnTpEgDwPMeowrzLlMZmaGpqysrM+vDDD1esWCErCgz7SRCE9vZ2URSZXY7jdF3Pycmtr6+/+QR7C6ANDQ0xMc6IiAgj3PCCEAgG/X19drsdCBkYCOXm5h46dEgUxZzc3L+1t9/ovyEIAkPAPkgAgICCIFBKL1269OCkSQDw7rvvPvzwHFlR2Hk6FAr19vaKosjiFVJqMolpaWnnzp0zwNw2PHEcx7KHCRPGy7JkUEpV1e6ebovFSilFxLjYWEEQEHHatGmapv318l8BgCIioCAKAlMxIsdzHo+np6dn2rRpDH1iQiJbjNVq7evrC4UGeJ5jvlNUJTExSdf1trY2xrE7AWXIzp9vyMjIlGXF4BMh0NnRabFY2G+KiIgECDsnnf7mNABoqioIwt69e7du3SqIgqaqLIwAwEMPPTREJEYNSm02a1eXV9epYVeS5IyMjJaWFibrkR4c8Zuto76+Pi4uLixBQUEQ29vb/X4/RQoAZpOJEKKoSkJCQmpKyom6EwAgmkxer3f9+vUvv/xyU1OT2WIBgK++qouIiBg/fryqqgDAjisAIMvK1attPM8zGXEsYI0dyyLozUWAkUAZM1paWjhC7Ha7ruu6rmuaTimllA4Eg7KsMNYCgCIrPM/PLij4+quvKKWiKK5cuTIhISE/P7+k5F+BEEQ8duz4lClTrFarLMsGUEQcDIV0XaeUUk3XdZ0imkwmh8PRdPHiPwV0eBekC42NaampkiTZ7XaTySQIAkcIE8twHKWOCMfhw4ePHj3a6fEEA8Ha2tpPP/105cqVzz//fH19w+5duwghzc3Nbrf7/fffdzgciMixtBqRDpeoBFG0WCySJCUlJba2tvT6fDcT9HsOdLNnzWpoaHjppZd4nmdFLwAQBJ4d0xBxx44dBj1ee+21jIwMADj151OdHR2iKEZGRu7evdsIh2VlZYjocrlYYDIiFM9zT618qqGhYf78J25Xw/oeoLNmzULELVu2GFMTQsxmkyAIxcXFGzZsCK9HsA7jx48fGAixaBD+8WQTPr1q1Zo1awRBMJvN4aNWr16NiIsWLQpfw22/9bfMUBlFmT2W1DGOVldXD52rqA74D84UFRWxnLWkpOTUqVMsdWSnC57n9+7bx3qyl0YmQCkNq6LdetPvdPCTJInn+enTZ9DhZrfbly1bVlZWNm/ePGaeI5yhQkLIspJlTApFRUUOh0PXdcYNtmYAmDlz5saNG0tLS51OJxtCKS0oKOB5PhQKDUvgf1MaIYTYbDYW1V588UUAyMvL6+np8fv958+flyTp+PHjDocDAHiOY2f22bNnI6WqokiShIjLli0DANNwvYTjuOoPPlBV9cL5C16vNxQKLVy4EACeWrlS0zSfz+d0OpnlH1IgKSwsZFY/+eSTzo7OyspKNtHYsWPr6+s//tOfjGoHABw8cJCdPWRZRsSvv/7aiNsxMTFvvvmmx+O5//772Zu1a9f6/f4jR46wTy5b1Q8smTAzU6ZMOXz4MJtu165dqSkp7N+01NRLTU3t7e1nz56ZNGlSWlqaJEmaqqmqqmmaoiiIOGvWrLS0tLq6uo6OjtaW1qlTp7KxCfHxr5SXszmPHz9eUFDwY4sl/PDg4uJiVmEMBAKbNm2KiYlm39WsrKy9b+/t7+8/efIkpVRRFE3VGFBd191ud5fXW1NTk5OTIwoCANjtNpfL1dvbi4jNzc3/9stf3u58/MMLona7vays7Pr164jY2tK6evVqURwKGuXl5YgoS7KmaQyopmuyJLPanTHV0qVLL1y4gIjBYHDTpk1RUVF3qP//2JpeWlranj172K6dOXPGKM+e/uY0Kzpr2pBHKaXt7e2M04899tgXXwyVHfft2zdh/IS7WC83LmUAID8/3yDu559/np+fX1paypSkqZqmakyC27Zty87OrqmpYT0/++yzmTNm3MVC7u3qzkVFRW63m4H45pvTiqJomqapqqYNSercuXOKLCPixYsXlz659Ccqjd+SuBaLxeVyeb1eRNQ0TZIkRVYUWZEkSVVVo1hpt9vDy28/2/VNUlLSrl3/NTg4GH59o2naW3v2pKam/pzXN7ck7oMPPvjWW281NDQ0Njbu37//7t4rjMoVowFrFK8Y75bOflLF/BgH37u3v9f+37W/A+hnRRw4+cSwAAAAAElFTkSuQmCC"


# ----- small helpers -----
def _rgb(color):
    color = color.lstrip("#")
    return tuple(int(color[i:i + 2], 16) for i in (0, 2, 4))


def mix(a, b, t):
    """Blend colour a towards colour b (t = 0..1)."""
    t = max(0.0, min(1.0, t))
    ra, rb = _rgb(a), _rgb(b)
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * t)) for x, y in zip(ra, rb))


def ease_out(t):
    return 1 - (1 - t) ** 3


def ease_in_out(t):
    return t * t * (3 - 2 * t)


def _bg_of(widget):
    try:
        return widget.cget("bg")
    except Exception:
        return SURFACE


def rr_points(x1, y1, x2, y2, r):
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
            x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


def round_rect(cv, x1, y1, x2, y2, r, **kw):
    return cv.create_polygon(rr_points(x1, y1, x2, y2, max(1, r)), smooth=True, **kw)


class Anim:
    """Tiny tween helper. Anim.run(widget, ms, fn, key=...) calls fn(eased 0..1) about 60 times a second;
    starting a new animation with the same key on the same widget replaces the running one."""

    @staticmethod
    def run(widget, ms, fn, ease=ease_out, done=None, key="a"):
        token = object()
        running = widget.__dict__.setdefault("_anims", {})
        running[key] = token
        start = time.perf_counter()

        def tick():
            if running.get(key) is not token:
                return
            try:
                t = min(1.0, (time.perf_counter() - start) * 1000.0 / max(1, ms))
                fn(ease(t))
                if t < 1.0:
                    widget.after(15, tick)
                elif done:
                    done()
            except tk.TclError:
                pass
        tick()


def apply_theme(root):
    """ttk is only used for the friends list and scrollbars."""
    root.configure(bg=BG)
    st = ttk.Style(root)
    st.theme_use("clam")
    st.configure(".", background=BG, foreground=FG, fieldbackground=SURFACE2, bordercolor=BORDER,
                 lightcolor=BG, darkcolor=BG, troughcolor=SURFACE2, focuscolor=ACCENT, font=FONT)
    st.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
    st.configure("Treeview", background=SURFACE, fieldbackground=SURFACE, foreground=FG,
                 borderwidth=0, relief="flat", rowheight=34, font=FONT)
    st.map("Treeview", background=[("selected", ACCENT_DARK)], foreground=[("selected", "#ffffff")])
    st.configure("Treeview.Heading", background=SURFACE2, foreground=MUTED, relief="flat",
                 borderwidth=0, font=("Segoe UI", 9, "bold"), padding=(8, 8))
    st.map("Treeview.Heading", background=[("active", SURFACE3)])
    st.configure("Friends.Treeview", rowheight=52)
    st.layout("Slim.Vertical.TScrollbar", [
        ("Vertical.Scrollbar.trough", {"sticky": "ns", "children": [
            ("Vertical.Scrollbar.thumb", {"expand": "1", "sticky": "nswe"})]})])
    st.configure("Slim.Vertical.TScrollbar", background=SURFACE3, troughcolor=SURFACE,
                 bordercolor=SURFACE, lightcolor=SURFACE3, darkcolor=SURFACE3, gripcount=0, width=8)
    st.map("Slim.Vertical.TScrollbar", background=[("active", ACCENT_DARK), ("pressed", ACCENT)])


# ----- vector icons (drawn, so they do not depend on any font) -----
def draw_icon(cv, kind, cx, cy, tag, col):
    line = dict(fill=col, width=2, capstyle="round", tags=tag)
    shape = dict(outline=col, width=2, tags=tag)
    if kind == "fleet":
        for dy, x2 in ((-8, 10), (0, 10), (8, 3)):
            cv.create_line(cx - 10, cy + dy, cx + x2, cy + dy, **line)
        cv.create_oval(cx + 6, cy + 5, cx + 12, cy + 11, **shape)
    elif kind == "profile":
        cv.create_oval(cx - 5, cy - 11, cx + 5, cy - 1, **shape)
        cv.create_arc(cx - 11, cy + 2, cx + 11, cy + 24, start=0, extent=180, style="arc", outline=col,
                      width=2, tags=tag)
    elif kind == "tune":
        for dx, ky in ((-8, -4), (0, 4), (8, -2)):
            cv.create_line(cx + dx, cy - 10, cx + dx, cy + 10, **line)
            cv.create_oval(cx + dx - 3, cy + ky - 3, cx + dx + 3, cy + ky + 3, **shape)
    elif kind == "guide":
        cv.create_oval(cx - 11, cy - 11, cx + 11, cy + 11, **shape)
        cv.create_text(cx, cy, text="?", fill=col, font=("Segoe UI", 11, "bold"), tags=tag)
    elif kind == "log":
        cv.create_line(cx - 10, cy - 6, cx - 3, cy, cx - 10, cy + 6, **line)
        cv.create_line(cx + 1, cy + 7, cx + 10, cy + 7, **line)
    elif kind == "home":
        cv.create_line(cx - 12, cy + 1, cx, cy - 11, cx + 12, cy + 1, **line)
        cv.create_line(cx - 8, cy - 2, cx - 8, cy + 11, cx + 8, cy + 11, cx + 8, cy - 2, **line)
    elif kind == "friend":
        cv.create_oval(cx - 12, cy - 9, cx - 3, cy, **shape)
        cv.create_oval(cx + 3, cy - 9, cx + 12, cy, **shape)
        cv.create_arc(cx - 15, cy + 2, cx + 1, cy + 20, start=0, extent=180, style="arc", outline=col, width=2, tags=tag)
        cv.create_arc(cx - 1, cy + 2, cx + 15, cy + 20, start=0, extent=180, style="arc", outline=col, width=2, tags=tag)
    elif kind == "rocket":
        draw_rocket(cv, cx, cy, 24, 1.0 if col != MUTED else 0.4, _bg_of(cv))
    elif kind == "game":
        cv.create_oval(cx - 11, cy - 11, cx + 11, cy + 11, **shape)
        cv.create_polygon(cx - 3, cy - 6, cx - 3, cy + 6, cx + 6, cy, fill=col, outline=col, tags=tag)
    elif kind == "target":
        cv.create_oval(cx - 11, cy - 11, cx + 11, cy + 11, **shape)
        cv.create_oval(cx - 4, cy - 4, cx + 4, cy + 4, **shape)
        cv.create_line(cx, cy - 15, cx, cy - 8, **line)
        cv.create_line(cx, cy + 8, cx, cy + 15, **line)


def paint_tag(cv, tag, col):
    for item in cv.find_withtag(tag):
        if cv.type(item) in ("line", "text"):
            cv.itemconfigure(item, fill=col)
        else:
            cv.itemconfigure(item, outline=col)


def rocket_points(cx, cy, s, flame):
    return [v for dx, dy in ((-0.1, 0.26), (0.0, 0.26 + 0.28 * flame), (0.1, 0.26)) for v in (cx + dx * s, cy + dy * s)]


def draw_rocket(cv, cx, cy, s, bv, bg, flame=1.0):
    """A small rocket. bv 0..1: dim outline-grey (off) to bright with a flame (on)."""
    col = mix("#4a4a4a", "#ffffff", bv)

    def pts(seq):
        return [v for dx, dy in seq for v in (cx + dx * s, cy + dy * s)]
    if bv > 0.05:
        cv.create_polygon(rocket_points(cx, cy, s, flame), fill=mix(bg, AMBER, bv), outline="", tags="flame")
    cv.create_polygon(pts(((-0.16, -0.02), (-0.36, 0.3), (-0.16, 0.24))), fill=col, outline="")
    cv.create_polygon(pts(((0.16, -0.02), (0.36, 0.3), (0.16, 0.24))), fill=col, outline="")
    cv.create_polygon(pts(((0, -0.52), (0.1, -0.36), (0.17, -0.12), (0.17, 0.26), (-0.17, 0.26), (-0.17, -0.12),
                           (-0.1, -0.36))), fill=col, outline="")
    cv.create_oval(cx - 0.07 * s, cy - 0.17 * s, cx + 0.07 * s, cy - 0.03 * s, fill=bg, outline="")


# ----- live mute for every running Roblox client -----
def set_clients_muted(muted):
    """Mutes/unmutes all running Roblox clients in the Windows volume mixer (needs: pip install pycaw comtypes).
    Returns how many clients were switched, or None when pycaw is not installed."""
    try:
        from pycaw.pycaw import AudioUtilities
    except Exception:
        return None
    count = 0
    try:
        for session in AudioUtilities.GetAllSessions():
            proc = session.Process
            try:
                name = proc.name() if proc else ""
            except Exception:
                continue
            if name.lower() == PROC_NAME.lower():
                session.SimpleAudioVolume.SetMute(1 if muted else 0, None)
                count += 1
    except Exception:
        return 0
    return count


class MuteButton(tk.Canvas):
    """Same look as the small ghost buttons. Speaker with sound waves that animate while sound is on,
    crossed-out speaker (no animation) while muted. Bound to a BooleanVar (True = muted)."""

    def __init__(self, master, variable, command=None, bg=None):
        super().__init__(master, width=88, height=30, bg=bg or _bg_of(master), highlightthickness=0, bd=0,
                         cursor="hand2")
        self._var, self._command = variable, command
        self._hover, self._phase = 0.0, 0
        self.bind("<Enter>", lambda _e: self._set_hover(1.0))
        self.bind("<Leave>", lambda _e: self._set_hover(0.0))
        self.bind("<ButtonRelease-1>", self._on_release)
        variable.trace_add("write", lambda *_: self._draw())
        self._draw()
        self._loop()

    def _set_hover(self, value):
        self._hover = value
        self._draw()

    def _on_release(self, e):
        if 0 <= e.x < self.winfo_width() and 0 <= e.y < self.winfo_height() and self._command:
            self._command()

    def _loop(self):
        try:
            if not self.winfo_exists():
                return
            if not self._var.get():
                self._phase += 1
                self._draw()
            self.after(320, self._loop)
        except tk.TclError:
            pass

    def _draw(self):
        try:
            self.delete("all")
            muted = bool(self._var.get())
            fill = mix("#0a0a0a", "#1c1c1c", self._hover)
            round_rect(self, 1, 1, 87, 29, 8, fill=fill, outline=fill)
            col = DIM if muted else "#ffffff"
            cx, cy = 20, 15
            self.create_polygon(cx - 8, cy - 3, cx - 4, cy - 3, cx + 1, cy - 8, cx + 1, cy + 8, cx - 4, cy + 3,
                                cx - 8, cy + 3, fill=col, outline=col)
            if muted:
                for a, b in (((cx + 5, cy - 5), (cx + 12, cy + 5)), ((cx + 5, cy + 5), (cx + 12, cy - 5))):
                    self.create_line(*a, *b, fill=DANGER, width=2, capstyle="round")
            else:
                for i in range(1 + self._phase % 3):
                    r = 5 + 4 * i
                    self.create_arc(cx + 1 - r, cy - r, cx + 1 + r, cy + r, start=-45, extent=90, style="arc",
                                    outline=col, width=2)
            self.create_text(60, 15, text="Unmute" if muted else "Mute", font=FONT_SMALL_B,
                             fill=mix(MUTED, "#ffffff", self._hover))
        except tk.TclError:
            pass


# ----- containers -----
class Card(tk.Frame):
    """A surface with a 1 px border. Put children into card.body."""

    def __init__(self, master, bg=SURFACE, **kw):
        super().__init__(master, bg=BORDER, **kw)
        self.body = tk.Frame(self, bg=bg)
        self.body.pack(fill="both", expand=True, padx=1, pady=1)


class Flow(tk.Frame):
    """Lays its children out left to right and wraps them into new rows (chips, keyword steps)."""

    def __init__(self, master, bg=SURFACE2, gap=6):
        super().__init__(master, bg=bg, height=1)
        self._gap, self._items = gap, []
        self.bind("<Configure>", self._relayout)

    def add(self, widget):
        self._items.append(widget)
        self.after_idle(self._relayout)
        return widget

    def _relayout(self, _event=None):
        if not self.winfo_exists():
            return
        limit = max(self.winfo_width(), 60)
        x = y = row_h = 0
        for widget in self._items:
            w, h = widget.winfo_reqwidth(), widget.winfo_reqheight()
            if x and x + w > limit:
                x, y, row_h = 0, y + row_h + self._gap, 0
            widget.place(x=x, y=y)
            x += w + self._gap
            row_h = max(row_h, h)
        total = y + row_h
        if total and int(float(self.cget("height"))) != total:
            self.configure(height=total)


class ScrollFrame(tk.Frame):
    """Vertically scrollable area; put children into .body."""

    def __init__(self, master, bg=SURFACE):
        super().__init__(master, bg=bg)
        self.canvas = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0)
        self.bar = ttk.Scrollbar(self, orient="vertical", style="Slim.Vertical.TScrollbar",
                                 command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.bar.set)
        self.bar.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.body = tk.Frame(self.canvas, bg=bg)
        self._win = self.canvas.create_window((0, 0), window=self.body, anchor="nw")
        self.body.bind("<Configure>", lambda _e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", lambda e: self.canvas.itemconfigure(self._win, width=e.width))
        self.bind_all("<MouseWheel>", self._wheel, add="+")

    def _wheel(self, event):
        try:
            widget = self.winfo_containing(event.x_root, event.y_root)
        except (KeyError, tk.TclError):
            return
        while widget is not None:
            if widget is self:
                if self.body.winfo_reqheight() > self.canvas.winfo_height():
                    self.canvas.yview_scroll(int(-event.delta / 120), "units")
                return
            widget = getattr(widget, "master", None)


class Collapsible(tk.Frame):
    """A panel that slides open and closed. Put children into .inner."""

    def __init__(self, master, bg=SURFACE):
        super().__init__(master, bg=bg, height=0)
        self.inner = tk.Frame(self, bg=bg)
        self.inner.place(x=0, y=0, relwidth=1)
        self.opened = False
        self._ch = 0

    def toggle(self, on_done=None):
        self.set_open(not self.opened, on_done)

    def set_open(self, state, on_done=None):
        self.opened = bool(state)
        if self.opened:
            try:
                self.grid()
            except tk.TclError:
                pass
        self.update_idletasks()
        target = self.inner.winfo_reqheight() if self.opened else 0
        start = self._ch

        def step(t):
            self._ch = int(start + (target - start) * t)
            self.configure(height=self._ch)
        def finished():
            if not self.opened:
                try:
                    self.grid_remove()
                except tk.TclError:
                    pass
            if on_done:
                on_done()
        Anim.run(self, 260, step, ease_in_out, done=finished, key="slide")


# ----- buttons and controls -----
class GlowButton(tk.Canvas):
    """Clean rounded button. The whole canvas is the hit area, it redraws to any size it is given.
    Supports .config(text=..., command=..., state='normal'|'disabled') like a normal button."""

    _KINDS = {  # base, hover, pressed, text, border
        "primary": ("#ffffff", "#e4e4e4", "#b8b8b8", "#000000", "#ffffff"),
        "secondary": ("#161616", "#242424", "#0c0c0c", "#ffffff", "#333333"),
        "danger": ("#160e0e", "#2a1414", "#0e0808", DANGER, "#4a2424"),
        "ghost": ("#0a0a0a", "#1c1c1c", "#121212", MUTED, "#0a0a0a"),
        "chip": ("#161616", "#242424", "#0c0c0c", "#ffffff", "#333333"),
    }

    def __init__(self, master, text="", command=None, kind="secondary", big=False, small=False,
                 shimmer=False, bg=None, **kw):
        font = FONT_BIG if big else (FONT_SMALL_B if small else FONT_BOLD)
        self._font = tkfont.Font(font=font)
        padx = 30 if big else (14 if small else 18)
        self._text, self._kind, self._command = text, kind, command
        self._state, self._t, self._down = "normal", 0.0, False
        self._fixed_w = kw.pop("width", None)
        self._ch = int(kw.pop("height", 0) or (52 if big else (30 if small else 38)))
        self._padx = padx
        self._cw = int(self._fixed_w or (self._font.measure(text) + 2 * padx))
        self._radius = 12 if big else (8 if small else 10)
        super().__init__(master, width=self._cw, height=self._ch, bg=bg or _bg_of(master),
                         highlightthickness=0, bd=0, cursor="hand2", **kw)
        self.bind("<Configure>", self._on_configure)
        self.bind("<Enter>", lambda _e: self._hover(True))
        self.bind("<Leave>", lambda _e: self._hover(False))
        self.bind("<ButtonPress-1>", self._on_press)
        self.bind("<ButtonRelease-1>", self._on_release)
        self._draw()

    # --- public API like a button ---
    def configure(self, cnf=None, **kw):
        if cnf:
            kw.update(cnf)
        command = kw.pop("command", _MISSING)
        state = kw.pop("state", None)
        text = kw.pop("text", None)
        if command is not _MISSING:
            self._command = command
        if text is not None and text != self._text:
            self._text = text
            if not self._fixed_w:
                self._cw = max(self._cw, self._font.measure(text) + 2 * self._padx)
                tk.Canvas.configure(self, width=self._cw)
            self._draw()
        if state is not None and state != self._state:
            self._state = state
            tk.Canvas.configure(self, cursor="arrow" if state == "disabled" else "hand2")
            self._apply()
        if kw:
            tk.Canvas.configure(self, **kw)

    config = configure

    def cget(self, key):
        if key == "text":
            return self._text
        if key == "state":
            return self._state
        return tk.Canvas.cget(self, key)

    # --- drawing ---
    def _on_configure(self, e):
        if e.width != self._cw or e.height != self._ch:
            self._cw, self._ch = e.width, e.height
            self._draw()

    def _fit(self, width):
        text = self._text
        if self._font.measure(text) <= width:
            return text
        while len(text) > 1 and self._font.measure(text + "\u2026") > width:
            text = text[:-1]
        return text + "\u2026"

    def _draw(self):
        self.delete("all")
        w, h = max(self._cw, 20), max(self._ch, 12)
        r = min(self._radius, h // 2)
        self._body = round_rect(self, 1, 1, w - 1, h - 1, r, width=1)
        self._label = self.create_text(w / 2, h / 2, text=self._fit(w - 16), fill=FG, font=self._font)
        self._apply()

    def _apply(self):
        base, hover, press, text, edge = self._KINDS[self._kind]
        if self._state == "disabled":
            fill, tcol, ec = "#0f0f0f", DIM, "#1c1c1c"
        elif self._down:
            fill, tcol, ec = press, text, edge
        else:
            fill, tcol = mix(base, hover, self._t), text
            ec = edge if self._kind == "primary" else mix(edge, "#7a7a7a", self._t)
        self.itemconfigure(self._body, fill=fill, outline=ec)
        self.itemconfigure(self._label, fill=tcol)
        self.coords(self._label, self._cw / 2, self._ch / 2 + (1 if self._down else 0))

    # --- interaction ---
    def _hover(self, on):
        if self._state == "disabled":
            return
        start = self._t
        target = 1.0 if on else 0.0
        if not on:
            self._down = False

        def step(t):
            self._t = start + (target - start) * t
            self._apply()
        Anim.run(self, 120, step, key="hover")

    def _on_press(self, _e):
        if self._state == "disabled":
            return
        self._down = True
        self._apply()
        try:
            self.focus_set()  # lets a text field lose focus
        except tk.TclError:
            pass

    def _on_release(self, e):
        was, self._down = self._down, False
        if self._state == "disabled":
            return
        self._apply()
        inside = 0 <= e.x < self.winfo_width() and 0 <= e.y < self.winfo_height()
        if was and inside and self._command:
            self._command()


class Switch(tk.Canvas):
    """On/off switch bound to a BooleanVar; the knob slides."""

    def __init__(self, master, variable, command=None, bg=SURFACE2):
        super().__init__(master, width=54, height=30, bg=bg, highlightthickness=0, bd=0, cursor="hand2")
        self._var, self._command = variable, command
        self._t = 1.0 if variable.get() else 0.0
        self.bind("<Button-1>", self._toggle)
        variable.trace_add("write", lambda *_: self._animate())
        self._draw()

    def _draw(self):
        t = self._t
        self.delete("all")
        track = mix("#262626", "#ffffff", t)
        self.create_oval(3, 4, 25, 26, fill=track, outline=track)
        self.create_oval(29, 4, 51, 26, fill=track, outline=track)
        self.create_rectangle(14, 4, 40, 26, fill=track, outline=track)
        x = 7 + 24 * t
        knob = mix("#8a8a8a", "#000000", t)
        self.create_oval(x, 8, x + 14, 22, fill=knob, outline=knob)

    def _animate(self):
        start, target = self._t, 1.0 if self._var.get() else 0.0

        def step(t):
            self._t = start + (target - start) * t
            self._draw()
        Anim.run(self, 180, step, key="slide")

    def _toggle(self, _e):
        self._var.set(not self._var.get())
        if self._command:
            self._command()


class Segmented(tk.Frame):
    """Segmented choice bound to a StringVar."""

    def __init__(self, master, variable, options):
        super().__init__(master, bg=SURFACE2, highlightthickness=1, highlightbackground=BORDER, bd=0)
        self._var, self._labels = variable, {}
        for value, text in options:
            lbl = tk.Label(self, text=text, font=FONT_BOLD, padx=16, pady=7, cursor="hand2", bg=SURFACE2, fg=MUTED)
            lbl.pack(side="left", padx=2, pady=2)
            lbl.bind("<Button-1>", lambda _e, v=value: variable.set(v))
            lbl.bind("<Enter>", lambda _e, v=value: self._hover(v, True))
            lbl.bind("<Leave>", lambda _e, v=value: self._hover(v, False))
            self._labels[value] = lbl
        variable.trace_add("write", lambda *_: self._paint())
        self._paint()

    def _hover(self, value, inside):
        if self._var.get() != value:
            self._labels[value].configure(bg=SURFACE3 if inside else SURFACE2)

    def _paint(self):
        for value, lbl in self._labels.items():
            selected = self._var.get() == value
            lbl.configure(bg="#ffffff" if selected else SURFACE2, fg="#000000" if selected else MUTED)


class ModeTiles(tk.Canvas):
    """Three selectable tiles bound to a StringVar; the whole tile is clickable and scales with the width."""

    def __init__(self, master, variable, options, bg=SURFACE):
        super().__init__(master, height=56, bg=bg, highlightthickness=0, bd=0, cursor="hand2")
        self._var, self._opts = variable, options
        self._t = {value: (1.0 if variable.get() == value else 0.0) for value, *_ in options}
        self._hover = None
        self.bind("<Configure>", lambda _e: self._draw())
        self.bind("<Button-1>", self._click)
        self.bind("<Motion>", self._motion)
        self.bind("<Leave>", lambda _e: self._set_hover(None))
        variable.trace_add("write", lambda *_: self._animate())

    def _gap(self):
        return 8

    def _geometry(self):
        n, gap = len(self._opts), self._gap()
        w = (max(self.winfo_width(), 240) - gap * (n - 1)) / n
        return [(i * (w + gap), i * (w + gap) + w) for i in range(n)]

    def _index_at(self, x):
        n = len(self._opts)
        total = max(self.winfo_width(), 1)
        return max(0, min(n - 1, int(x * n / total)))

    def _motion(self, e):
        self._set_hover(self._opts[self._index_at(e.x)][0])

    def _set_hover(self, value):
        if value != self._hover:
            self._hover = value
            self._draw()

    def _click(self, e):
        self._var.set(self._opts[self._index_at(e.x)][0])

    def _animate(self):
        start = dict(self._t)
        target = {v: (1.0 if self._var.get() == v else 0.0) for v, *_ in self._opts}

        def step(t):
            for v in self._t:
                self._t[v] = start[v] + (target[v] - start[v]) * t
            self._draw()
        Anim.run(self, 200, step, key="tiles")

    def _draw(self):
        self.delete("all")
        h = int(float(self.cget("height")))
        for (x1, x2), (value, title, _sub, icon) in zip(self._geometry(), self._opts):
            t = self._t.get(value, 0.0)
            hov = 0.5 if self._hover == value and t < 0.5 else 0.0
            fill = mix(mix(SURFACE2, SURFACE3, hov), "#1f1f1f", t)
            edge = mix(mix(BORDER, "#4a4a4a", hov), "#ffffff", t)
            round_rect(self, x1 + 1, 1, x2 - 1, h - 1, 12, fill=fill, outline=edge, width=2 if t > 0.5 else 1)
            col = mix(MUTED, "#ffffff", t)
            draw_icon(self, icon, x1 + 28, h / 2, f"ic_{value}", col)
            self.create_text(x1 + 52, h / 2, text=title, anchor="w", fill=col, font=FONT_BOLD)


class StatTile(tk.Canvas):
    """Big number with a label; the number counts up or down smoothly."""

    def __init__(self, master, label, color, bg=SURFACE):
        super().__init__(master, height=74, bg=bg, highlightthickness=0, bd=0)
        self._label, self._color, self._value, self._shown = label, color, 0, 0.0
        self.bind("<Configure>", lambda _e: self._draw())

    def set(self, value):
        value = int(value)
        if value == self._value:
            return
        start = self._shown
        self._value = value

        def step(t):
            self._shown = start + (value - start) * t
            self._draw()
        Anim.run(self, 420, step, key="count")

    def _draw(self):
        self.delete("all")
        w, h = max(self.winfo_width(), 100), int(float(self.cget("height")))
        round_rect(self, 1, 1, w - 1, h - 1, 14, fill=SURFACE2, outline=BORDER)
        round_rect(self, 12, 16, 15, h - 16, 1, fill=self._color, outline="")
        self.create_text(30, h / 2 - 7, text=str(int(round(self._shown))), anchor="w", fill=FG, font=FONT_NUM)
        self.create_text(30, h - 16, text=self._label, anchor="w", fill=MUTED, font=FONT_SMALL)


class GlowProgress(tk.Canvas):
    """Slim progress bar: smooth steps, or a travelling glow while the length is unknown."""

    def __init__(self, master, bg=SURFACE, width=170, height=8):
        super().__init__(master, width=width, height=height, bg=bg, highlightthickness=0, bd=0)
        self._mode, self._frac, self._phase, self._busy_job = "idle", 0.0, 0.0, None
        self.bind("<Configure>", lambda _e: self._draw())

    def set_idle(self):
        self._stop_busy()
        self._mode = "idle"
        self._to(0.0)

    def set_steps(self, total, done):
        self._stop_busy()
        self._mode = "steps"
        self._to(done / max(1, total))

    def set_busy(self):
        if self._mode == "busy":
            return
        self._mode = "busy"
        self._busy_loop()

    def _to(self, target):
        start = self._frac

        def step(t):
            self._frac = start + (target - start) * t
            self._draw()
        Anim.run(self, 260, step, key="fill")

    def _stop_busy(self):
        if self._busy_job is not None:
            try:
                self.after_cancel(self._busy_job)
            except tk.TclError:
                pass
            self._busy_job = None

    def _busy_loop(self):
        if self._mode != "busy":
            return
        self._phase = (self._phase + 0.025) % 1.0
        self._draw()
        try:
            self._busy_job = self.after(33, self._busy_loop)
        except tk.TclError:
            pass

    def _draw(self):
        self.delete("all")
        w, h = max(self.winfo_width(), 40), int(float(self.cget("height")))
        r = h / 2
        round_rect(self, 0, 0, w, h, r, fill=SURFACE3, outline="")
        if self._mode == "busy":
            seg = w * 0.34
            x = -seg + (w + seg) * self._phase
            x1, x2 = max(0, x), min(w, x + seg)
            if x2 - x1 > 3:
                round_rect(self, x1, 0, x2, h, r, fill=ACCENT, outline="")
        elif self._frac > 0.002:
            end = max(h, w * self._frac)
            round_rect(self, 0, 0, end, h, r, fill=ACCENT, outline="")
            round_rect(self, max(0, end - h * 2.2), 0, end, h, r, fill=ACCENT2, outline="")


class HintEntry(tk.Entry):
    """Entry that shows a grey example text while it is empty.
    get() returns '' while the example is shown, so the rest of the program never sees it."""

    def __init__(self, master, hint="", show="", **kw):
        opts = dict(bg=INPUT, fg=FG, insertbackground=FG, relief="flat", bd=7, font=FONT,
                    highlightthickness=1, highlightbackground=BORDER, highlightcolor=ACCENT,
                    selectbackground=ACCENT_DARK, selectforeground="#ffffff")
        opts.update(kw)
        super().__init__(master, **opts)
        self._hint, self._real_show, self._showing = hint, show, False
        self.bind("<FocusIn>", lambda _e: self._clear_hint(), add="+")
        self.bind("<FocusOut>", lambda _e: self._put_hint(), add="+")
        self._put_hint()

    def _put_hint(self):
        if self._showing or tk.Entry.get(self):
            return
        tk.Entry.configure(self, show="", fg=DIM)
        tk.Entry.insert(self, 0, self._hint)
        self._showing = True

    def _clear_hint(self):
        if not self._showing:
            return
        tk.Entry.delete(self, 0, "end")
        tk.Entry.configure(self, show=self._real_show, fg=FG)
        self._showing = False

    def _has_focus(self):
        try:
            return self.focus_get() is self
        except (KeyError, tk.TclError):
            return False

    def get(self):
        return "" if self._showing else tk.Entry.get(self)

    def delete(self, first, last=None):
        if self._showing:
            return
        tk.Entry.delete(self, first, last)
        if not tk.Entry.get(self) and not self._has_focus():
            self._put_hint()

    def insert(self, index, string):
        self._clear_hint()
        tk.Entry.insert(self, index, string)


class HintText(tk.Text):
    """Multi-line text field with a grey example text while it is empty (normal Text.get() works)."""

    def __init__(self, master, hint="", **kw):
        opts = dict(bg=INPUT, fg=FG, insertbackground=FG, relief="flat", bd=0, font=FONT, wrap="word",
                    highlightthickness=1, highlightbackground=BORDER, highlightcolor=ACCENT,
                    padx=8, pady=7, selectbackground=ACCENT_DARK, selectforeground="#ffffff")
        opts.update(kw)
        super().__init__(master, **opts)
        self._hint = tk.Label(self, text=hint, bg=opts["bg"], fg=DIM, font=FONT, justify="left", anchor="nw")
        self._hint.bind("<Button-1>", lambda _e: (self.focus_set(), "break")[1])
        for sequence in ("<KeyRelease>", "<<Paste>>", "<<Cut>>", "<FocusOut>"):
            self.bind(sequence, lambda _e: self.after_idle(self.sync), add="+")
        self.sync()

    def sync(self):
        """Show or hide the example text (call after changing the content from code)."""
        if self.get("1.0", "end-1c"):
            self._hint.place_forget()
        else:
            self._hint.place(x=10, y=8)


# ----- navigation -----
class SideNav(tk.Canvas):
    """Slim sidebar: logo, icon tabs with a sliding highlight, and a status orb at the bottom."""

    ITEM_H = 72

    def __init__(self, master, items, command):
        super().__init__(master, width=92, bg=BG, highlightthickness=0, bd=0)
        self._items, self._cmd, self._sel, self._hover = items, command, None, None
        self._top = 112
        self._tile_y = None
        self._logo = tk.PhotoImage(data=_LOGO_PNG_B64)
        self.create_image(46, 54, image=self._logo)
        self._tile = round_rect(self, 8, 0, 84, 10, 14, fill=SURFACE3, outline=BORDER, state="hidden")
        self._bar = round_rect(self, 0, 0, 3, 10, 1, fill=ACCENT, outline="", state="hidden")
        for i, (key, label, icon) in enumerate(items):
            cy = self._top + i * self.ITEM_H + 22
            draw_icon(self, icon, 46, cy, f"i_{key}", MUTED)
            self.create_text(46, cy + 27, text=label, fill=MUTED, font=FONT_SMALL_B, tags=f"t_{key}")
        self._orb_halo = self.create_oval(0, 0, 0, 0, fill=SURFACE3, outline="")
        self._orb = self.create_oval(0, 0, 0, 0, fill=GREEN, outline="")
        self._orb_color, self._orb_pulse = GREEN, False
        self.bind("<Configure>", lambda _e: self._place_orb(0.0))
        self.bind("<Motion>", self._motion)
        self.bind("<Leave>", lambda _e: self._set_hover(None))
        self.bind("<Button-1>", self._click)

    def _index_at(self, y):
        i = int((y - self._top) // self.ITEM_H)
        return i if 0 <= i < len(self._items) else None

    def _motion(self, e):
        i = self._index_at(e.y)
        key = self._items[i][0] if i is not None else None
        self.configure(cursor="hand2" if key else "")
        self._set_hover(key)

    def _set_hover(self, key):
        if key != self._hover:
            self._hover = key
            self._paint()

    def _click(self, e):
        i = self._index_at(e.y)
        if i is not None:
            self._cmd(self._items[i][0])

    def _paint(self):
        for key, _label, _icon in self._items:
            if key == self._sel:
                icon_col, text_col = "#ffffff", "#ffffff"
            elif key == self._hover:
                icon_col, text_col = FG, FG
            else:
                icon_col, text_col = MUTED, DIM
            paint_tag(self, f"i_{key}", icon_col)
            self.itemconfigure(f"t_{key}", fill=text_col)

    def _put_tile(self, y):
        self._tile_y = y
        self.coords(self._tile, *rr_points(8, y, 84, y + self.ITEM_H - 8, 14))
        self.coords(self._bar, *rr_points(0, y + 16, 3, y + self.ITEM_H - 24, 1))
        self.itemconfigure(self._tile, state="normal")
        self.itemconfigure(self._bar, state="normal")
        self.tag_lower(self._tile)
        self.tag_raise(self._bar)

    def select(self, key):
        index = [k for k, *_ in self._items].index(key)
        target = self._top + index * self.ITEM_H - 2
        self._sel = key
        self._paint()
        if self._tile_y is None:
            self._put_tile(target)
            return
        start = self._tile_y
        Anim.run(self, 260, lambda t: self._put_tile(start + (target - start) * t), ease_out, key="tile")

    # --- status orb ---
    def _place_orb(self, phase):
        h = max(self.winfo_height(), 400)
        cx, cy = 46, h - 40
        halo = 10 + (4 * (0.5 + 0.5 * math.sin(phase)) if self._orb_pulse else 0)
        self.coords(self._orb_halo, cx - halo, cy - halo, cx + halo, cy + halo)
        self.coords(self._orb, cx - 5, cy - 5, cx + 5, cy + 5)
        self.itemconfigure(self._orb_halo, fill=mix(BG, self._orb_color, 0.22))
        self.itemconfigure(self._orb, fill=self._orb_color)

    def set_orb(self, color, pulse):
        self._orb_color, self._orb_pulse = color, pulse
        self._place_orb(0.0)

    def pulse(self, phase):
        if self._orb_pulse:
            self._place_orb(phase)


def draw_character(cv, cx, cy, s, skin, shirt, pants, tag="char"):
    """A small blocky Roblox-style character, s = total height. Scales cleanly to any size."""
    top = cy - s / 2
    r = max(1, s * 0.05)

    def box(x1, y1, x2, y2, col, rad=0):
        if rad:
            round_rect(cv, cx + x1 * s, top + y1 * s, cx + x2 * s, top + y2 * s, rad, fill=col, outline="", tags=tag)
        else:
            cv.create_rectangle(cx + x1 * s, top + y1 * s, cx + x2 * s, top + y2 * s, fill=col, outline="", tags=tag)
    box(-0.34, 0.29, -0.19, 0.60, skin)           # arms
    box(0.19, 0.29, 0.34, 0.60, skin)
    box(-0.17, 0.28, 0.17, 0.62, shirt)           # torso
    box(-0.34, 0.29, -0.19, 0.41, shirt)          # sleeves
    box(0.19, 0.29, 0.34, 0.41, shirt)
    box(-0.17, 0.63, -0.005, 1.0, pants)          # legs
    box(0.005, 0.63, 0.17, 1.0, pants)
    box(-0.15, 0.0, 0.15, 0.26, skin, rad=r * 1.6)  # head
    e = max(1.0, s * 0.022)
    for ex in (-0.055, 0.055):
        cv.create_oval(cx + ex * s - e, top + 0.12 * s - e, cx + ex * s + e, top + 0.12 * s + e,
                       fill="#111111", outline="", tags=tag)


class AccountList(tk.Frame):
    """One canvas per account: character, names, live status with a pulsing dot and an animated check box.
    The whole card is a single click target."""

    ROW_H = 72
    _SKIN = ("#f2c9a0", "#e0ac84", "#c68a62", "#8d5a3b", "#f6d7b8", "#ffe0a8")
    _SHIRT = ("#4f8cff", "#ef4d5d", "#34c38f", "#f5b83d", "#9b6bff", "#ff7aa8", "#2dd4bf", "#f08a3c")
    _PANTS = ("#2b3a67", "#3b3b4f", "#244c3a", "#5a3d2b", "#40306b", "#35505c")
    _DOT = {"run": GREEN, "warn": AMBER, "bad": DANGER, "idle": DIM, "ok": BLUE, "off": DIM}
    _TXT = {"run": GREEN, "warn": AMBER, "bad": DANGER}

    def __init__(self, master, on_toggle, state_of, is_checked):
        super().__init__(master, bg=SURFACE)
        self._on_toggle, self._state_of, self._is_checked = on_toggle, state_of, is_checked
        self.scroll = ScrollFrame(self, bg=SURFACE)
        self.scroll.pack(fill="both", expand=True)
        self.body = self.scroll.body
        self.body.columnconfigure(0, weight=1)
        self.rows, self._names = {}, None
        self._filter, self._imgs, self.on_menu = "", {}, None
        self.is_boosted, self.on_boost = (lambda _n: False), None
        self.on_relaunch, self.is_relaunch = None, (lambda _n: False)
        self._f_name = tkfont.Font(font=FONT_BOLD)
        self._f_small = tkfont.Font(font=FONT_SMALL)
        self._empty = None

    def set_filter(self, text):
        self._filter = (text or "").strip().lower()

    def sync(self, accounts):
        f = self._filter
        view = [a for a in accounts if not f or f in a["name"].lower() or f in (a.get("display") or "").lower()]
        names = [a["name"] for a in view]
        if names != self._names:
            self._rebuild(view, bool(accounts))
        self.refresh(view)

    def set_avatar(self, name, data):
        try:
            self._imgs[name] = tk.PhotoImage(data=data)
        except tk.TclError:
            return
        info = self.rows.get(name)
        if info:
            self._draw(info)

    def _rebuild(self, accounts, any_accounts=True):
        for child in self.body.winfo_children():
            child.destroy()
        self.rows, self._names = {}, [a["name"] for a in accounts]
        if not accounts:
            self._empty = tk.Label(self.body, text="No matches" if any_accounts else "No accounts yet",
                                   bg=SURFACE, fg=DIM, font=FONT, pady=40)
            self._empty.grid(row=0, column=0, sticky="ew")
            return
        for i, acc in enumerate(accounts):
            self._make_row(i, acc)

    def _make_row(self, index, acc):
        name = acc["name"]
        cv = tk.Canvas(self.body, height=self.ROW_H, width=10, bg=SURFACE, highlightthickness=0, bd=0,
                       cursor="hand2")
        cv.grid(row=index, column=0, sticky="ew", pady=(0, 8), padx=(0, 8))
        seed = sum(map(ord, name))
        info = dict(cv=cv, name=name, tag="off", sel=None, t=0.0, hover=False, status="", sub="",
                    boost=None, bv=0.0, pop=0.0, rl=False, spin=0.0, rlgeo=(0, 0), appear=0.0, rx=0, rocket=(0, 0, 0),
                    skin=self._SKIN[seed % len(self._SKIN)], shirt=self._SHIRT[seed % len(self._SHIRT)],
                    pants=self._PANTS[(seed // 3) % len(self._PANTS)])
        self.rows[name] = info
        cv.bind("<Configure>", lambda _e, i=info: self._draw(i))
        cv.bind("<Button-1>", lambda e, i=info: self._click(i, e))
        cv.bind("<Motion>", lambda e, i=info: cv.configure(cursor="hand2"))

        def reveal(i=info, c=cv):
            def step(v):
                i["appear"] = v
                self._draw(i)
            Anim.run(c, 300, step, key="appear")
        cv.after(30 + index * 35, reveal)
        cv.bind("<Enter>", lambda _e, i=info: self._set_hover(i, True))
        cv.bind("<Leave>", lambda _e, i=info: self._set_hover(i, False))
        cv.bind("<Button-3>", lambda e, n=name: self.on_menu(n, e.x_root, e.y_root) if self.on_menu else None)

    def _click(self, info, event):
        if self.on_relaunch and abs(event.x - (info["rx"] - 34)) <= 15:
            self.on_relaunch(info["name"])
        elif self.on_boost and abs(event.x - info["rx"]) <= 18:
            self.on_boost(info["name"])
        else:
            self._on_toggle(info["name"])

    @staticmethod
    def _arrow(cx, cy, spin):
        """Start angle of the arc and the arrow head polygon for a circular arrow turned by `spin` degrees."""
        start = 60 + spin
        end = math.radians(start + 290)
        r = 7
        px, py = cx + r * math.cos(end), cy - r * math.sin(end)
        nx, ny = math.cos(end), -math.sin(end)
        tx, ty = -math.sin(end), -math.cos(end)
        return start, (px + tx * 6, py + ty * 6, px + nx * 4.5, py + ny * 4.5, px - nx * 4.5, py - ny * 4.5)

    def _set_hover(self, info, on):
        if info["hover"] != on:
            info["hover"] = on
            self._draw(info)

    @staticmethod
    def _ellipsize(font, text, width):
        if font.measure(text) <= width:
            return text
        while len(text) > 1 and font.measure(text + "\u2026") > width:
            text = text[:-1]
        return text + "\u2026"

    def _draw(self, info):
        cv = info["cv"]
        try:
            w = max(cv.winfo_width(), 200)
        except tk.TclError:
            return
        h = self.ROW_H
        k = info["appear"]

        def F(col):
            return col if k >= 0.999 else mix(SURFACE, col, k)
        sel, t = bool(info["sel"]), info["t"]
        bg = SURFACE3 if info["hover"] else SURFACE2
        edge = mix(mix(BORDER, "#555555", 1.0 if info["hover"] else 0.0), "#ffffff", t)
        cv.delete("all")
        round_rect(cv, 1, 1, w - 1, h - 1, 14, fill=F(bg), outline=F(edge), width=2 if t > 0.5 else 1)
        tile = h - 12
        round_rect(cv, 10, 6, 10 + tile, 6 + tile, 10, fill=F("#0b0b0b"), outline=F(BORDER))
        if k >= 0.95:
            img = self._imgs.get(info["name"])
            if img is not None:
                cv.create_image(10 + tile / 2, 6 + tile / 2, image=img)
            else:
                draw_character(cv, 10 + tile / 2, 6 + tile / 2 + 1, tile * 0.8, info["skin"], info["shirt"],
                               info["pants"])
        # check box (far right)
        cb = 24
        cx2 = w - 14 - cb
        cy1 = (h - cb) / 2
        round_rect(cv, cx2, cy1, cx2 + cb, cy1 + cb, 7, fill=F(mix(bg, "#ffffff", t)),
                   outline=F(mix("#555555", "#ffffff", t)), width=2)
        if t > 0.35:
            kk = min(1.0, (t - 0.35) / 0.65)
            cv.create_line(cx2 + 6, cy1 + 12.5, cx2 + 10.5, cy1 + 17, fill="#000000", width=2.5, capstyle="round")
            if kk > 0.5:
                cv.create_line(cx2 + 10.5, cy1 + 17, cx2 + 18, cy1 + 8, fill="#000000", width=2.5, capstyle="round")
        # performance rocket (left of the check box)
        rx = cx2 - 26
        info["rx"] = rx
        scale = 1 + 0.35 * math.sin(math.pi * info["pop"])
        size = 24 * scale
        draw_rocket(cv, rx, h / 2 + 1, size, info["bv"], bg)
        info["rocket"] = (rx, h / 2 + 1, size)
        # relaunch switch (circular arrow, left of the rocket): spins while automatic relaunch is on
        lx = rx - 34
        on = bool(info["rl"])
        icol = F("#ffffff" if (on or info["hover"]) else "#6f6f6f")
        start, head = self._arrow(lx, h / 2, info["spin"] if on else 0)
        cv.create_arc(lx - 7, h / 2 - 7, lx + 7, h / 2 + 7, start=start, extent=290, style="arc", outline=icol,
                      width=2, tags="rl")
        cv.create_polygon(*head, fill=icol, outline=icol, tags="rlh")
        info["rlgeo"] = (lx, h / 2)
        # status
        status = info["status"]
        tcol = self._TXT.get(info["tag"], MUTED)
        sx = rx - 58
        status_w = min(self._f_small.measure(status), max(60, (w - 260) // 2))
        status = self._ellipsize(self._f_small, status, status_w)
        cv.create_text(sx, h / 2, text=status, anchor="e", fill=F(tcol), font=FONT_SMALL)
        dot_x = sx - self._f_small.measure(status) - 14
        cv.create_oval(dot_x - 5, h / 2 - 5, dot_x + 5, h / 2 + 5, fill=F(self._DOT.get(info["tag"], DIM)),
                       outline="", tags="dot")
        # names
        nx = 10 + tile + 14
        room = max(40, dot_x - 14 - nx)
        cv.create_text(nx, h / 2 - 9, text=self._ellipsize(self._f_name, info["name"], room), anchor="w",
                       fill=F(FG), font=FONT_BOLD)
        if info["sub"]:
            cv.create_text(nx, h / 2 + 11, text=self._ellipsize(self._f_small, info["sub"], room), anchor="w",
                           fill=F(MUTED), font=FONT_SMALL)

    def refresh(self, accounts):
        for acc in accounts:
            info = self.rows.get(acc["name"])
            if not info:
                continue
            boost = bool(self.is_boosted(acc["name"]))
            if info["boost"] is None:
                info["boost"], info["bv"] = boost, (1.0 if boost else 0.0)
                self._draw(info)
            elif boost != info["boost"]:
                info["boost"] = boost
                start, goal = info["bv"], (1.0 if boost else 0.0)

                def step(v, i=info, s=start, g=goal):
                    i["bv"] = s + (g - s) * v
                    i["pop"] = v if v < 1.0 else 0.0
                    self._draw(i)
                Anim.run(info["cv"], 320, step, key="boost")
            rl = bool(self.is_relaunch(acc["name"]))
            relaunch_changed = rl != info["rl"]
            info["rl"] = rl
            text, tag = self._state_of(acc)
            sub = acc.get("display") or ""
            changed = relaunch_changed or (text, tag, sub) != (info["status"], info["tag"], info["sub"])
            info["status"], info["tag"], info["sub"] = text, tag, sub
            sel = bool(self._is_checked(acc["name"]))
            if sel != info["sel"]:
                first = info["sel"] is None
                info["sel"] = sel
                target = 1.0 if sel else 0.0
                if first:
                    info["t"] = target
                    changed = True
                else:
                    start = info["t"]

                    def step(t, i=info, s=start, g=target):
                        i["t"] = s + (g - s) * t
                        self._draw(i)
                    Anim.run(info["cv"], 180, step, key="check")
            if changed:
                self._draw(info)

    def pulse(self, phase):
        k = 0.5 + 0.5 * math.sin(phase)
        for info in self.rows.values():
            try:
                if info["tag"] == "run":
                    info["cv"].itemconfigure("dot", fill=mix(GREEN, SURFACE2, 0.55 * k))
                if info["rl"] and info["appear"] >= 0.999:
                    info["spin"] = (info["spin"] - 32) % 360
                    lx, ly = info["rlgeo"]
                    start, head = self._arrow(lx, ly, info["spin"])
                    info["cv"].itemconfigure("rl", start=start)
                    info["cv"].coords("rlh", *head)
                if info["boost"] and info["appear"] >= 0.999:
                    rx, ry, size = info["rocket"]
                    flame = 0.7 + 0.6 * (0.5 + 0.5 * math.sin(phase * 3 + hash(info["name"]) % 7))
                    info["cv"].coords("flame", *rocket_points(rx, ry, size, flame))
            except tk.TclError:
                pass


# --------------------------------------------------------------------------
# App
# --------------------------------------------------------------------------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry("1340x880")
        self.minsize(1180, 760)
        apply_theme(self)
        # A callback exception used to tear the mainloop down; now a child
        # Toplevel error (grab races, destroy on a dying widget, etc.) is
        # swallowed and logged so the main window stays open.
        self.report_callback_exception = self._swallow_callback_error
        # Background threads: a raised exception used to show in stderr and
        # surface as the custom error popup; keep the worker gone, keep the
        # main window alive and intact.
        try:
            threading.excepthook = self._swallow_thread_error
        except Exception:
            pass
        self.accounts = load_accounts()
        self.settings = load_settings()
        self.performance_mode = tk.BooleanVar(value=self.settings["performance_mode"])
        self.extreme_save_mode = tk.BooleanVar(value=self.settings["extreme_save_mode"])
        self.auto_recovery = tk.BooleanVar(value=self.settings.get("auto_recovery", False))
        self.lean_clients = tk.BooleanVar(value=self.settings.get("lean_clients", True))
        self.fps_cap = tk.StringVar(value=str(self.settings.get("fps_cap", 30)))
        self.launch_speed = tk.StringVar(value=self.settings.get("launch_speed", "fast"))
        self.mute_clients = tk.BooleanVar(value=self.settings.get("mute_clients", False))
        self.perf_off = set(self.settings.get("perf_off", []))
        self.auto_tile = tk.BooleanVar(value=self.settings.get("auto_tile", False))
        self.tiny_windows = tk.BooleanVar(value=self.settings.get("tiny_windows", False))
        self.recent_games = list(self.settings.get("recent_games", []))
        self.auto_fix = tk.BooleanVar(value=self.settings.get("auto_fix", True))
        self._auto_fix_on = bool(self.auto_fix.get())
        self._login_failures = 0
        self._last_message_t = 0.0
        self.progress = {"active": False, "label": "", "total": 1, "done": 0, "ok": 0, "frac": 0.0,
                         "stage": "", "name": "", "t0": 0.0, "acct_t0": 0.0,
                         "phase": "run", "done_until": 0.0, "est0": 0.0}
        self._prog_tick_on = False
        self.launch_hist = []
        self.login_mode = tk.StringVar(value=self.settings.get("login_mode", "safe"))
        LOGIN_MODE["mode"] = "normal" if self.login_mode.get() == "smart" else self.login_mode.get()
        self._login_choice = self.login_mode.get()
        self._speed_choice = self.launch_speed.get()
        self.net = {"state": "ok", "ms": 0}
        self.login_state = {}
        self.flag_packs = {k: tk.BooleanVar(value=k in self.settings.get("flag_packs", [])) for k in FLAG_PACKS}
        self.relaunch_on = set(self.settings.get("relaunch_on", []))
        self.always_on_top = tk.BooleanVar(value=self.settings.get("always_on_top", False))
        self.specific_users = list(self.settings.get("specific_users", []))
        self.target_user = None
        self.checked = set()
        self.friend_cache = []
        self.friend_imgs = {}
        self.tracked = {}
        self.launch_lock = threading.Lock()
        self.login_lock = threading.Lock()
        self._sessions_lock = threading.RLock()
        self.session_cache = {}
        self._join_cache = {}
        self.friend_owners = {}
        self.busy = False
        self.closing = False
        self._launch_cancel_event = threading.Event()
        # One shared cancellation switch for every launcher-owned operation.
        # Unlike closing the app, this deliberately leaves the UI usable.
        self._action_cancel_event = threading.Event()
        self.jobs = ActionQueue(self._jobs_changed, self.log)
        self._job_cancel_any = AnyEvent(self.jobs.current_cancel, self._action_cancel_event)
        self._stopping = False
        self._last_message = ("READY", "Waiting for an action.")
        self._problems = []
        self._status_job = None
        self._tick_scheduled = False
        self._limit_names = set()
        self._limit_lock = threading.Lock()
        _RATE.cancel = self._cancelled
        _RATE.log = self.log
        self._monitor_event = threading.Event()
        self._shutdown_event = threading.Event()
        self._build()
        self.mute_clients.trace_add("write", lambda *_: self._on_mute_changed())
        self.after(1500, self._mute_loop)
        self._dark_titlebar()
        self._apply_speed()
        self._on_window_option_silent()
        self._refresh_list()
        hold_singleton_mutex()
        self._report_multi_instance()
        threading.Thread(target=self._net_loop, name="NetCheck", daemon=True).start()
        self.after(200, self._restore_friends)
        threading.Thread(target=self._cookie_loop, name="CookieKeeper", daemon=True).start()
        self.after(2500, lambda: self.load_friends(auto=True))
        for migration_message in MIGRATION_MESSAGES:
            self.log(migration_message)
        self.log(f"Ready. Data folder: {DATA_DIR}")
        if self.performance_mode.get():
            self.log("Performance Mode is enabled by default.")
        if not find_edge():
            self.log("Warning: Microsoft Edge was not found.")
        threading.Thread(target=self._watchdog, name="CrimsonWatchdog", daemon=True).start()
        self.after(80, lambda: threading.Thread(target=self._warmup, name="CrimsonWarmup", daemon=True).start())
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------- UI ----------
    _PAGES = (("fleet", "Fleet", "fleet"), ("profile", "Profile", "profile"), ("tune", "Tune", "tune"),
              ("log", "Log", "log"))
    _PAGE_TITLES = {"fleet": "Fleet", "profile": "Profile", "tune": "Tune", "log": "Log"}

    @staticmethod
    def _autowrap(label, container, margin):
        """Keep a label's wrap length in step with the width of its container."""
        container.bind("<Configure>", lambda e: label.configure(wraplength=max(220, e.width - margin)), add="+")

    def _build(self):
        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)
        self.pages = {}
        self._page = None
        self._set_icon()
        self.nav = SideNav(self, [(k, label, icon) for k, label, icon in self._PAGES], self.show_page)
        self.nav.grid(row=0, column=0, sticky="ns")
        main = tk.Frame(self, bg=BG)
        main.grid(row=0, column=1, sticky="nsew", padx=(0, 18))
        main.columnconfigure(0, weight=1)
        main.rowconfigure(1, weight=1)
        self._build_topbar(main)
        self.page_host = tk.Frame(main, bg=BG)
        self.page_host.grid(row=1, column=0, sticky="nsew")
        builders = {"fleet": self._build_fleet_page, "profile": self._build_profile_page,
                    "tune": self._build_tune_page, "log": self._build_log_page}
        for key, builder in builders.items():
            page = tk.Frame(self.page_host, bg=BG)
            self.pages[key] = page
            panel = page if key == "fleet" else Card(page, bg=SURFACE)
            if key != "fleet":
                panel.pack(fill="both", expand=True)
                panel = panel.body
            builder(panel)
        self._build_dock(main)
        self._render_saved_users()
        self.show_page("fleet")
        self._phase = 0.0
        self._avatar_shown, self._avatar_fresh, self._avatar_busy, self._avatar_try = {}, set(), False, 0.0
        self._bind_shortcuts()
        self.after(400, self._anim_loop)

    def _set_icon(self):
        try:
            self._icon_image = tk.PhotoImage(data=_ICON_PNG_B64)
            self.iconphoto(True, self._icon_image)
        except tk.TclError:
            pass

    def _dark_titlebar(self):
        """Dark window title bar on Windows 10/11 (silently skipped elsewhere)."""
        if os.name != "nt":
            return
        try:
            self.update_idletasks()
            user32 = ctypes.WinDLL("user32")
            user32.GetParent.argtypes = [wintypes.HWND]
            user32.GetParent.restype = wintypes.HWND
            hwnd = user32.GetParent(self.winfo_id())
            value = ctypes.c_int(1)
            for attribute in (20, 19):
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(
                        hwnd, attribute, ctypes.byref(value), ctypes.sizeof(value)) == 0:
                    break
        except Exception:
            pass

    def _anim_loop(self):
        """One shared heartbeat (about 11 fps) for the pulsing status dots and the sidebar orb."""
        if self.closing:
            return
        self._phase += 0.55
        try:
            self.alist.pulse(self._phase)
            self.nav.pulse(self._phase)
        except Exception:
            pass
        self.after(90, self._anim_loop)

    # --- page switching with a short slide-in ---
    def show_page(self, key):
        page = self.pages.get(key)
        if page is None or key == self._page:
            return
        old = self.pages.get(self._page)
        self._page = key
        self.page_title.config(text=self._PAGE_TITLES[key])
        self.nav.select(key)
        page.place(x=46, y=0, relwidth=1, relheight=1)
        page.tkraise()
        host_old = old

        def step(t):
            page.place_configure(x=int(46 * (1 - t)))
        def done():
            if host_old is not None and host_old is not page:
                host_old.place_forget()
        Anim.run(page, 240, step, ease_out, done=done, key="slide")

    # --- top bar ---
    def _build_topbar(self, main):
        bar = tk.Frame(main, bg=BG)
        bar.grid(row=0, column=0, sticky="ew", pady=(18, 12))
        bar.columnconfigure(0, weight=1)
        left = tk.Frame(bar, bg=BG)
        left.grid(row=0, column=0, sticky="w")
        self.page_title = tk.Label(left, text="", bg=BG, fg=FG, font=FONT_TITLE)
        self.page_title.pack(anchor="w")
        self.header_state = tk.Label(bar, text="READY")  # kept for the backend, not shown (the bottom bar says it)
        badges = tk.Frame(bar, bg=BG)
        badges.grid(row=0, column=1, padx=(0, 16))
        self.net_badge = tk.Label(badges, text="", bg=BG, fg=MUTED, font=FONT_SMALL_B)
        self.net_badge.pack(side="left", padx=(0, 14))
        self.multi_badge = tk.Label(badges, text="", bg=BG, fg=MUTED, font=FONT_SMALL_B)
        self.multi_badge.pack(side="left")
        self.multi_badge.bind("<Button-1>", lambda _e: None if MULTI["ok"] else self.fix_multi_instance())
        self.btn_stop_all = GlowButton(bar, text="STOP ALL", kind="danger", command=self.stop_all_actions, bg=BG)
        self.btn_stop_all.grid(row=0, column=2)

    # --- Fleet page: accounts on the left, mission on the right ---
    def _build_fleet_page(self, page):
        page.columnconfigure(0, weight=3, minsize=400)
        page.columnconfigure(1, weight=2, minsize=470)
        page.rowconfigure(0, weight=1)
        left = Card(page)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 12))
        right = Card(page)
        right.grid(row=0, column=1, sticky="nsew")
        self._build_accounts_panel(left.body)
        self._build_mission_panel(right.body)

    def _build_accounts_panel(self, box):
        box.columnconfigure(0, weight=1)
        box.rowconfigure(3, weight=1)
        top = tk.Frame(box, bg=SURFACE)
        top.grid(row=0, column=0, sticky="ew", padx=16, pady=(16, 10))
        top.columnconfigure(1, weight=1)
        tk.Label(top, text="Accounts", bg=SURFACE, fg=FG, font=FONT_H2).grid(row=0, column=0, sticky="w")
        self.e_search = HintEntry(top, hint="Search")
        self.e_search.grid(row=0, column=1, sticky="ew", padx=14, ipady=2)
        self.e_search.bind("<KeyRelease>", lambda _e: self._on_search(), add="+")
        self.btn_add = GlowButton(top, text="+ Add", kind="primary", small=True, command=self._toggle_add_panel)
        self.btn_add.grid(row=0, column=2, sticky="ns")

        self.add_panel = Collapsible(box)
        self.add_panel.grid(row=1, column=0, sticky="ew", padx=16)
        self.add_panel.grid_remove()
        form = self.add_panel.inner
        form.columnconfigure(0, weight=1, uniform="addcols")
        form.columnconfigure(1, weight=1, uniform="addcols")
        self.e_user = HintEntry(form, hint="Username")
        self.e_pass = HintEntry(form, hint="Password", show="•")
        self.e_user.grid(row=0, column=0, sticky="ew", padx=(0, 5), ipady=2)
        self.e_pass.grid(row=0, column=1, sticky="ew", padx=(5, 0), ipady=2)
        self.e_pass.bind("<Return>", lambda _e: self.add_account(False))
        GlowButton(form, text="Save", command=lambda: self.add_account(False)).grid(
            row=1, column=0, sticky="ew", padx=(0, 5), pady=(8, 0))
        GlowButton(form, text="Save and log in", kind="primary", command=lambda: self.add_account(True)).grid(
            row=1, column=1, sticky="ew", padx=(5, 0), pady=(8, 0))
        tk.Frame(form, bg=SURFACE, height=12).grid(row=2, column=0, columnspan=2)

        info = tk.Frame(box, bg=SURFACE)
        info.grid(row=2, column=0, sticky="ew", padx=16, pady=(0, 8))
        info.columnconfigure(0, weight=1)
        self.acc_count = tk.Label(info, text="", bg=SURFACE, fg=MUTED, font=FONT_SMALL, anchor="w")
        self.acc_count.grid(row=0, column=0, sticky="ew")
        GlowButton(info, text="\u21bb Relaunch", kind="ghost", small=True,
                   command=self.relaunch_selected).grid(row=0, column=2, sticky="e")

        self.alist = AccountList(box, self._toggle_account, self._card_state, lambda n: n in self.checked)
        self.alist.on_menu = self._account_menu
        self.alist.is_boosted = self._boosted
        self.alist.on_boost = self.toggle_boost
        self.alist.on_relaunch = self.toggle_relaunch
        self.alist.is_relaunch = self._relaunch_wanted
        self.alist.grid(row=3, column=0, sticky="nsew", padx=(16, 8))

        actions = tk.Frame(box, bg=SURFACE)
        actions.grid(row=4, column=0, sticky="ew", padx=16, pady=(8, 16))
        GlowButton(actions, text="Select all", command=self.select_all, small=True).pack(side="left")
        GlowButton(actions, text="Clear", command=self.clear_all, small=True).pack(side="left", padx=(6, 0))
        GlowButton(actions, text="Log in again", command=self.relogin_selected, small=True).pack(side="left", padx=(6, 0))
        GlowButton(actions, text="Remove", kind="danger", command=self.remove_selected, small=True).pack(side="right")

    def _on_search(self):
        self.alist.set_filter(self.e_search.get())
        self._refresh_list()

    def _toggle_add_panel(self):
        opening = not self.add_panel.opened
        self.btn_add.config(text="Close" if opening else "+ Add")
        self.add_panel.toggle()
        if opening:
            self.after(280, self.e_user.focus_set)

    # --- mission panel: where to go + launch ---
    def _build_mission_panel(self, box):
        box.columnconfigure(0, weight=1)
        box.rowconfigure(2, weight=1)
        tk.Label(box, text="Mission", bg=SURFACE, fg=FG, font=FONT_H2).grid(
            row=0, column=0, sticky="w", padx=16, pady=(16, 10))
        self.mode = tk.StringVar(value="app")
        ModeTiles(box, self.mode, [("app", "Home", "", "home"), ("game", "Game", "", "game"),
                                   ("friend", "Friend", "", "friend"), ("user", "User", "", "target")]).grid(row=1, column=0, sticky="ew", padx=16)
        stage = tk.Frame(box, bg=SURFACE)
        stage.grid(row=2, column=0, sticky="nsew", padx=16, pady=(12, 0))
        stage.columnconfigure(0, weight=1)
        stage.rowconfigure(0, weight=1)
        # one panel per mode, only the active one is shown
        home = tk.Frame(stage, bg=SURFACE)
        tk.Label(home, text="Starts Roblox on its home screen", bg=SURFACE, fg=DIM, font=FONT_SMALL).place(
            relx=0.5, rely=0.5, anchor="center")
        game = tk.Frame(stage, bg=SURFACE)
        game.columnconfigure(0, weight=1)
        self.e_place = HintEntry(game, hint="Game ID or link")
        self.e_place.grid(row=0, column=0, sticky="ew", ipady=2)
        self.e_place.bind("<Return>", lambda _e: self.check_game())
        GlowButton(game, text="Check", command=self.check_game).grid(row=0, column=1, padx=(8, 0), sticky="ns")
        self.e_job = HintEntry(game, hint="Server ID (optional)")
        self.e_job.grid(row=1, column=0, columnspan=2, sticky="ew", ipady=2, pady=(8, 0))
        self.game_info = tk.Label(game, text="", bg=SURFACE, fg=MUTED, font=FONT_SMALL, anchor="w", justify="left")
        self.game_info.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))
        self.recent_games_frame = tk.Frame(game, bg=SURFACE)
        self.recent_games_frame.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        user = tk.Frame(stage, bg=SURFACE)
        user.columnconfigure(0, weight=1)
        self.e_target = HintEntry(user, hint="Username or display name")
        self.e_target.grid(row=0, column=0, sticky="ew", ipady=2)
        self.e_target.bind("<Return>", lambda _e: self.add_specific_user())
        GlowButton(user, text="Add", command=self.add_specific_user).grid(row=0, column=1, padx=(8, 0), sticky="ns")
        GlowButton(user, text="Follow", command=self.follow_specific_user).grid(row=0, column=2, padx=(6, 0), sticky="ns")
        self.saved_users_frame = tk.Frame(user, bg=SURFACE)
        self.saved_users_frame.grid(row=1, column=0, columnspan=3, sticky="ew", pady=(10, 0))
        fbox = tk.Frame(stage, bg=SURFACE)
        fbox.columnconfigure(0, weight=1)
        fbox.rowconfigure(1, weight=1)
        head = tk.Frame(fbox, bg=SURFACE)
        head.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        head.columnconfigure(0, weight=1)
        GlowButton(head, text="Reload friends", command=self.load_friends, small=True).grid(row=0, column=1)
        fw = tk.Frame(fbox, bg=SURFACE, highlightthickness=1, highlightbackground=BORDER)
        fw.grid(row=1, column=0, sticky="nsew")
        fw.columnconfigure(0, weight=1)
        fw.rowconfigure(0, weight=1)
        self.friend_list = ttk.Treeview(fw, columns=("status", "accs"), style="Friends.Treeview",
                                        selectmode="browse")
        self.friend_list.heading("#0", text="Friend", anchor="w")
        self.friend_list.heading("status", text="Status", anchor="w")
        self.friend_list.heading("accs", text="Accounts", anchor="center")
        self.friend_list.column("#0", width=250, stretch=True)
        self.friend_list.column("status", width=80, stretch=False)
        self.friend_list.column("accs", width=86, stretch=False, anchor="center")
        friends_scroll = ttk.Scrollbar(fw, orient="vertical", style="Slim.Vertical.TScrollbar",
                                       command=self.friend_list.yview)
        self.friend_list.configure(yscrollcommand=friends_scroll.set)
        self.friend_list.grid(row=0, column=0, sticky="nsew")
        friends_scroll.grid(row=0, column=1, sticky="ns")
        self.friend_list.tag_configure("ingame", foreground=GREEN)
        self.friend_list.tag_configure("online", foreground=BLUE)
        self.friend_list.tag_configure("offline", foreground=MUTED)
        self.friend_list.bind("<<TreeviewSelect>>", lambda _e: self.mode.set("friend")
                              if self.friend_list.selection() else None)
        self._stage = {"app": home, "game": game, "user": user, "friend": fbox}
        self._render_recent_games()
        for frame in self._stage.values():
            frame.grid(row=0, column=0, sticky="nsew")
        self.mode.trace_add("write", lambda *_: self._show_stage())
        self._show_stage()

        dock = tk.Frame(box, bg=SURFACE)
        dock.grid(row=3, column=0, sticky="ew", padx=16, pady=(14, 16))
        dock.columnconfigure(0, weight=1, uniform="dock")
        dock.columnconfigure(1, weight=1, uniform="dock")
        self.btn_launch = GlowButton(dock, text="LAUNCH SELECTED", kind="primary", big=True, command=self.launch)
        self.btn_launch.grid(row=0, column=0, columnspan=2, sticky="ew")
        GlowButton(dock, text="Restart selected", command=self.restart_all).grid(
            row=1, column=0, sticky="ew", padx=(0, 4), pady=(8, 0))
        GlowButton(dock, text="Stop selected", command=self.stop_selected).grid(
            row=1, column=1, sticky="ew", padx=(4, 0), pady=(8, 0))
        GlowButton(dock, text="Tile windows", kind="ghost", command=self.tile_windows).grid(
            row=2, column=0, columnspan=2, sticky="ew", pady=(8, 0))

    # --- Join game ID ---
    def _game_name(self, place_id):
        return next((g.get("name", "") for g in self.recent_games if int(g.get("id", 0)) == int(place_id)), "")

    def _remember_game(self, place_id, name=""):
        name = name or self._game_name(place_id)
        self.recent_games = [{"id": int(place_id), "name": name}] + [
            g for g in self.recent_games if int(g.get("id", 0)) != int(place_id)]
        self.recent_games = self.recent_games[:8]
        self._persist_settings()
        self._render_recent_games()

    def _render_recent_games(self):
        frame = getattr(self, "recent_games_frame", None)
        if frame is None:
            return
        for child in frame.winfo_children():
            child.destroy()
        flow = Flow(frame, bg=SURFACE)
        flow.pack(fill="x")
        for game in self.recent_games:
            label = (game.get("name") or str(game["id"]))[:22]
            chip = GlowButton(flow, text=label, kind="chip", small=True, command=lambda g=game: self._use_recent_game(g))
            chip.bind("<Button-3>", lambda _e, g=game: self._forget_recent_game(g))
            flow.add(chip)

    def _use_recent_game(self, game):
        self.e_place.delete(0, "end")
        self.e_place.insert(0, str(game["id"]))
        self.mode.set("game")
        self.check_game()

    def _forget_recent_game(self, game):
        self.recent_games = [g for g in self.recent_games if int(g.get("id", 0)) != int(game["id"])]
        self._persist_settings()
        self._render_recent_games()

    # ---------- progress with time elapsed and about how long is left ----------
    def _prog_avg(self):
        recent = self.launch_hist[-4:]
        return (sum(recent) / len(recent)) if recent else SPEED_EST.get(getattr(self, "_speed_key", "fast"), 25)

    def _prog_kick(self):
        if not self._prog_tick_on:
            self._prog_tick_on = True
            try:
                self.after(0, self._prog_tick)
            except (tk.TclError, RuntimeError):
                self._prog_tick_on = False

    def _prog_visible(self):
        return self.progress["active"] or time.monotonic() < self.progress.get("done_until", 0.0)

    def _prog_start(self, label, total):
        """Press Start: first the time is worked out (a moment), then 'Starting process'."""
        p = self.progress
        now = time.monotonic()
        total = max(1, total)
        p.update(active=True, phase="calc", label=label, total=total, done=0, ok=0, frac=0.0,
                 stage="Calculating time ...", name="", t0=now, acct_t0=now, done_until=0.0,
                 est0=total * self._prog_avg())
        self._prog_kick()
        if threading.current_thread() is not threading.main_thread():
            self._launch_cancel_event.wait(1.0)
        now = time.monotonic()
        p.update(phase="run", t0=now, acct_t0=now, stage="Starting process", left=None, left_t=now)

    def _prog_stage(self, name, text, frac=None):
        """What the launcher is doing right now (any thread). frac = how far the current account is (0-1)."""
        p = self.progress
        if not p["active"]:
            return
        new_account = bool(name) and name != p["name"]
        if new_account:
            p["name"], p["acct_t0"], p["frac"] = name, time.monotonic(), 0.0
        p["stage"] = f"{name}  \u00b7  {text}" if name else text
        if frac is not None:
            p["frac"] = max(p["frac"], frac)

    def _stage_frac(self, frac):
        if self.progress["active"]:
            self.progress["frac"] = max(self.progress["frac"], frac)

    def _prog_account_done(self, ok):
        p = self.progress
        if not p["active"]:
            return
        now = time.monotonic()
        if ok:
            if p["label"] in ("Launching", "Restarting"):
                self.launch_hist = (self.launch_hist + [now - p["acct_t0"]])[-6:]
            p["ok"] += 1
        p["done"] += 1
        p["frac"], p["acct_t0"], p["name"] = 0.0, now, ""

    def _prog_end(self):
        p = self.progress
        if p["active"]:
            now = time.monotonic()
            p.update(active=False, phase="done", t_end=now, done_until=now + 8.0, frac=1.0,
                     stopped=bool(self._launch_cancel_event.is_set()))
            self._prog_kick()
        try:
            self.after(0, self._render_status)
        except (tk.TclError, RuntimeError):
            pass

    def _prog_eta(self):
        """Seconds left, worked out again from how the current account is really doing."""
        p = self.progress
        avg = self._prog_avg()
        if p["phase"] == "calc":
            return p["est0"]
        now = time.monotonic()
        elapsed, frac = now - p["acct_t0"], p["frac"]
        stable = float(STABLE_SECONDS) + 1.0
        busy = bool(p["name"])
        left_cur, scale = 0.0, 1.0
        if busy:
            if frac >= 0.65:  # Roblox is open, the check that it stays open is running
                left_cur = stable * max(0.0, 0.95 - frac) / 0.3 + 1.0
            else:             # waiting for Roblox to open
                expected_open = max(avg - stable, 8.0)
                if elapsed < expected_open:
                    left_cur = expected_open - elapsed + stable
                else:         # slower than usual: the guess grows with the delay
                    left_cur = max(4.0, 0.25 * elapsed) + stable
            if elapsed > avg:
                scale = min(2.5, elapsed / max(avg, 1.0))
        later = max(0, p["total"] - p["done"] - (1 if busy else 0))
        return left_cur + later * (avg * scale + LAUNCH_PAUSE)

    def _prog_left(self):
        """The countdown shown as 'Time left': it runs down every second, goes up when things are slower than
        expected and drops faster when they are quicker."""
        p = self.progress
        now = time.monotonic()
        target = self._prog_eta()
        prev = p.get("left")
        if prev is None:
            left = target
        else:
            left = prev - (now - p.get("left_t", now))
            if target > left + 8:
                left = target
            elif target < left - 1:
                left -= min(left - target, max(2.0, (left - target) * 0.5))
        left = max(0.0, left)
        p["left"], p["left_t"] = left, now
        return left

    def _prog_tick(self):
        if self.closing or not self._prog_visible():
            self._prog_tick_on = False
            if not self.closing:
                try:
                    self._render_status()
                except tk.TclError:
                    pass
            return
        self._render_status()
        self.after(1000, self._prog_tick)

    def _render_progress(self):
        p = self.progress
        if p["phase"] == "done" and not p["active"]:
            total_time = fmt_clock(p.get("t_end", time.monotonic()) - p["t0"])
            self.activity_state.set("STOPPED" if p.get("stopped") else "DONE")
            self.activity_title.set(("Stopped" if p.get("stopped") else "Finished process")
                                    + f"     {p['ok']} of {p['total']} running     {total_time} in total")
            self.activity_detail.set("All clients are running." if p["ok"] == p["total"] and not p.get("stopped")
                                     else "Check the log for the accounts that did not start.")
            self._set_progress_mode("steps", 100, 100 if p["ok"] == p["total"] else int(100 * p["ok"] / max(1, p["total"])))
            return
        elapsed = time.monotonic() - p["t0"]
        shown = min(p["done"] + 1, p["total"])
        if p["phase"] == "calc":
            left = "calculating time ..."
        else:
            eta = self._prog_left()
            left = f"Time left {fmt_clock(eta)}" if eta >= 1 else "finishing ..."
        self.activity_state.set("LAUNCHING")
        self.activity_title.set(f"{p['label']}  {shown} of {p['total']}     {fmt_clock(elapsed)} elapsed     {left}")
        self.activity_detail.set(p["stage"])
        pct = int(100 * min(1.0, (p["done"] + p["frac"]) / max(1, p["total"])))
        self._set_progress_mode("steps", 100, pct)

    def _type_text(self, kind):
        if kind == "speed":
            key = self.launch_speed.get()
            return f"About {SPEED_EST.get(key, 25)} s per account.  {SPEED_TEXT.get(key, '')}"
        key = self.login_mode.get()
        return f"About {LOGIN_EST.get(key, 8)} s per login.  {LOGIN_TEXT.get(key, '')}"

    def check_game(self):
        """Look the typed game up and show its name and how many are playing."""
        place_id = parse_game_id(self.e_place.get())
        if not place_id:
            self.game_info.config(text="Enter a game ID or paste a game link.", fg=DANGER)
            return
        self.game_info.config(text="Looking up the game ...", fg=MUTED)

        def work():
            info = lookup_game(place_id)
            def show():
                if info:
                    self.game_info.config(text=f"{info['name']}  \u00b7  {info['playing']:,} playing", fg=GREEN)
                    self._remember_game(place_id, info["name"])
                else:
                    hint = self._net_hint(True) if self.net["state"] != "ok" else ""
                    self.game_info.config(text=("Game not found. " + hint).strip(), fg=DANGER)
            try:
                self.after(0, show)
            except (tk.TclError, RuntimeError):
                pass
        threading.Thread(target=work, daemon=True, name="GameLookup").start()

    def _show_stage(self):
        mode = self.mode.get()
        for key, frame in self._stage.items():
            if key == mode:
                frame.grid()
            else:
                frame.grid_remove()

    # saved users (chips under the user field)
    def _render_saved_users(self):
        frame = getattr(self, "saved_users_frame", None)
        if frame is None:
            return
        for child in frame.winfo_children():
            child.destroy()
        flow = Flow(frame, bg=SURFACE)
        flow.pack(fill="x")
        for user in self.specific_users:
            chip = GlowButton(flow, text="@" + str(user["name"]), kind="chip", small=True,
                              command=lambda u=user: self._use_saved_user(u))
            chip.bind("<Button-3>", lambda _e, u=user: self._forget_saved_user(u))
            flow.add(chip)

    def _use_saved_user(self, user):
        self.target_user = (int(user["id"]), str(user["name"]), str(user.get("displayName", user["name"])))
        self.e_target.delete(0, "end")
        self.e_target.insert(0, str(user["name"]))
        self.mode.set("user")

    def _forget_saved_user(self, user):
        uid = int(user["id"])
        self.specific_users = [u for u in self.specific_users if int(u.get("id", 0)) != uid]
        if self.target_user and self.target_user[0] == uid:
            self.target_user = None
        self._persist_settings()
        self._render_saved_users()

    # --- Profile page ---
    def _build_profile_page(self, page):
        page.columnconfigure(0, weight=1)
        card = Card(page, bg=SURFACE2)
        card.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 0))
        box = card.body
        box.columnconfigure(0, weight=1)
        tk.Label(box, text="Display name", bg=SURFACE2, fg=FG, font=FONT_BOLD).grid(
            row=0, column=0, columnspan=2, sticky="w", padx=14, pady=(12, 8))
        self.e_display_name = HintEntry(box, hint="New display name")
        self.e_display_name.grid(row=1, column=0, sticky="ew", padx=(14, 8), pady=(0, 14), ipady=2)
        GlowButton(box, text="Apply", kind="primary", command=self.change_display_name).grid(
            row=1, column=1, padx=(0, 14), pady=(0, 14), sticky="ns")
        card = Card(page, bg=SURFACE2)
        card.grid(row=1, column=0, sticky="ew", padx=18, pady=(12, 18))
        box = card.body
        box.columnconfigure(0, weight=1)
        tk.Label(box, text="Bio", bg=SURFACE2, fg=FG, font=FONT_BOLD).grid(
            row=0, column=0, sticky="w", padx=14, pady=(12, 8))
        self.bio_count = tk.Label(box, text="0 / 1000", bg=SURFACE2, fg=MUTED, font=FONT_SMALL)
        self.bio_count.grid(row=0, column=1, sticky="e", padx=14, pady=(12, 8))
        self.e_bio = HintText(box, hint="New bio", height=5)
        self.e_bio.grid(row=1, column=0, columnspan=2, sticky="ew", padx=14)
        self.e_bio.bind("<KeyRelease>", lambda _e: self._update_bio_counter(), add="+")
        GlowButton(box, text="Apply", kind="primary", command=self.change_bio).grid(
            row=2, column=0, columnspan=2, sticky="e", padx=14, pady=(10, 14))

    def _update_bio_counter(self):
        count = len(self.e_bio.get("1.0", "end-1c"))
        self.bio_count.config(text=f"{count} / 1000", fg=DANGER if count > 1000 else MUTED)

    # --- Tune page ---
    def _setting_row(self, page, row, title, text, variable, command=None):
        card = Card(page, bg=SURFACE2)
        card.grid(row=row, column=0, sticky="ew", padx=18, pady=(18 if row == 0 else 10, 0))
        box = card.body
        box.columnconfigure(0, weight=1)
        tk.Label(box, text=title, bg=SURFACE2, fg=FG, font=FONT_BOLD).grid(
            row=0, column=0, sticky="w", padx=14, pady=(12, 2))
        label = tk.Label(box, text=text, bg=SURFACE2, fg=MUTED, font=FONT_SMALL, justify="left", anchor="w")
        label.grid(row=1, column=0, sticky="ew", padx=(14, 8), pady=(0, 12))
        self._autowrap(label, box, 110)
        Switch(box, variable, command=command or self._on_optimization_changed, bg=SURFACE2).grid(
            row=0, column=1, rowspan=2, padx=16)
        return box

    def _card_row(self, page, row, title, text):
        card = Card(page, bg=SURFACE2)
        card.grid(row=row, column=0, sticky="ew", padx=18, pady=(18 if row == 0 else 10, 0))
        box = card.body
        box.columnconfigure(0, weight=1)
        tk.Label(box, text=title, bg=SURFACE2, fg=FG, font=FONT_BOLD).grid(
            row=0, column=0, sticky="w", padx=14, pady=(12, 2))
        if text:
            tk.Label(box, text=text, bg=SURFACE2, fg=MUTED, font=FONT_SMALL, justify="left", anchor="w").grid(
                row=1, column=0, sticky="ew", padx=14, pady=(0, 10))
        return box

    def _build_tune_page(self, page):
        scroll = ScrollFrame(page, bg=SURFACE)
        scroll.pack(fill="both", expand=True)
        page = scroll.body
        page.columnconfigure(0, weight=1)
        pre = self._card_row(page, 0, "Presets", "One tap sets performance mode, lean clients and frame-rate cap.")
        prow = tk.Frame(pre, bg=SURFACE2)
        prow.grid(row=2, column=0, sticky="ew", padx=14, pady=(2, 14))
        for col in range(3):
            prow.columnconfigure(col, weight=1, uniform="presets")
        for col, (key, label) in enumerate((("potato", "Potato"), ("balanced", "Balanced"), ("off", "Off"))):
            GlowButton(prow, text=label, kind="primary" if key == "potato" else "secondary",
                       command=lambda k=key: self.apply_preset(k)).grid(
                row=0, column=col, sticky="ew", padx=(0 if col == 0 else 4, 0 if col == 2 else 4))
        fix = self._setting_row(page, 1, "Auto-fix", "Repairs problems by itself: damaged Roblox settings, multi-instance, expired logins, a wrong clock, leftovers after failed starts.",
                                self.auto_fix, command=self._on_auto_fix)
        GlowButton(fix, text="Fix everything now", kind="primary", command=self.fix_everything).grid(
            row=2, column=0, columnspan=2, sticky="w", padx=14, pady=(0, 14))
        self._setting_row(page, 2, "Performance mode", "Lowest graphics for accounts with a rocket. All others get the highest graphics at 120 FPS.",
                          self.performance_mode)
        lean = self._setting_row(page, 3, "Lean clients", "A frame-rate cap for lighter clients.",
                                 self.lean_clients)
        cap_row = tk.Frame(lean, bg=SURFACE2)
        cap_row.grid(row=2, column=0, columnspan=2, sticky="w", padx=14, pady=(0, 14))
        tk.Label(cap_row, text="Frame-rate cap", bg=SURFACE2, fg=MUTED, font=FONT_SMALL).pack(side="left", padx=(0, 12))
        Segmented(cap_row, self.fps_cap, [("15", "15"), ("30", "30"), ("60", "60"), ("0", "Off")]).pack(side="left")
        self.fps_cap.trace_add("write", lambda *_: self._on_optimization_changed())
        speed = self._card_row(page, 5, "Launch speed", "Pause between client starts.")
        speed_row = tk.Frame(speed, bg=SURFACE2)
        speed_row.grid(row=2, column=0, sticky="w", padx=14, pady=(0, 14))
        Segmented(speed_row, self.launch_speed, [("smart", "Smart"), ("slow", "Slow"), ("safe", "Safe"), ("fast", "Fast"), ("instant", "Instant")]).pack()
        self.launch_speed.trace_add("write", lambda *_: self._on_speed_changed())
        self.speed_desc = tk.StringVar(value=self._type_text("speed"))
        tk.Label(speed, textvariable=self.speed_desc, bg=SURFACE2, fg=MUTED, font=FONT_SMALL, anchor="w",
                 justify="left", wraplength=520).grid(row=3, column=0, sticky="w", padx=14, pady=(0, 12))
        login = self._card_row(page, 6, "Login method", "How Edge signs accounts in. Only used when a saved login has expired.")
        login_row = tk.Frame(login, bg=SURFACE2)
        login_row.grid(row=2, column=0, sticky="w", padx=14, pady=(0, 14))
        Segmented(login_row, self.login_mode, [("smart", "Smart"), ("slow", "Slow"), ("safe", "Safe"), ("normal", "Normal"), ("fast", "Fast")]).pack()
        self.login_mode.trace_add("write", lambda *_: self._on_login_mode())
        self.login_desc = tk.StringVar(value=self._type_text("login"))
        tk.Label(login, textvariable=self.login_desc, bg=SURFACE2, fg=MUTED, font=FONT_SMALL, anchor="w",
                 justify="left", wraplength=520).grid(row=3, column=0, sticky="w", padx=14, pady=(0, 12))
        self._setting_row(page, 7, "Extreme save mode", "Fewer checks and parallel workers. For many accounts.",
                          self.extreme_save_mode)
        flags = self._card_row(page, 9, "Custom flags", "Your own Roblox fast flags as JSON. Applied to every client.")
        self.e_flags = HintText(flags, hint='{"DFIntTaskSchedulerTargetFps": 60}', height=4, font=FONT_MONO)
        self.e_flags.grid(row=2, column=0, columnspan=2, sticky="ew", padx=14)
        saved = load_custom_flags()
        if saved:
            self.e_flags.insert("1.0", json.dumps(saved, indent=2))
            self.e_flags.sync()
        GlowButton(flags, text="Save flags", command=self.save_flags, small=True).grid(
            row=3, column=0, columnspan=2, sticky="e", padx=14, pady=(8, 14))
        self._setting_row(page, 8, "Tiny windows", "Small client windows render far fewer pixels. Arranged after every launch.",
                          self.tiny_windows, command=self._on_window_option)
        self._setting_row(page, 10, "Auto-arrange windows", "Tile the Roblox windows after every launch.",
                          self.auto_tile, command=self._on_window_option)
        self._setting_row(page, 11, "Always on top", "Keep this launcher above other windows.",
                          self.always_on_top, command=self._on_window_option)
        packs = self._card_row(page, 13, "Flag packs", "Extra Roblox fast flags for every client. Applied at the next start.")
        for index, (key, (title, text, _flags)) in enumerate(FLAG_PACKS.items()):
            row = tk.Frame(packs, bg=SURFACE2)
            row.grid(row=2 + index, column=0, columnspan=2, sticky="ew", padx=14, pady=(0, 10))
            row.columnconfigure(0, weight=1)
            tk.Label(row, text=title, bg=SURFACE2, fg=FG, font=FONT_SMALL, anchor="w").grid(row=0, column=0, sticky="w")
            tk.Label(row, text=text, bg=SURFACE2, fg=MUTED, font=FONT_SMALL, anchor="w", justify="left",
                     wraplength=520).grid(row=1, column=0, sticky="w")
            Switch(row, self.flag_packs[key], command=self._on_flag_pack, bg=SURFACE2).grid(
                row=0, column=1, rowspan=2, padx=(8, 2))
        tools = self._card_row(page, 12, "Tools", "")
        trow = tk.Frame(tools, bg=SURFACE2)
        trow.grid(row=2, column=0, sticky="ew", padx=14, pady=(4, 14))
        for col in range(5):
            trow.columnconfigure(col, weight=1, uniform="tools")
        GlowButton(trow, text="Fix multi-instance", command=self.fix_multi_instance).grid(
            row=0, column=0, sticky="ew", padx=(0, 4))
        GlowButton(trow, text="Clear Roblox logs", command=self.clear_cache).grid(
            row=0, column=1, sticky="ew", padx=4)
        GlowButton(trow, text="Tile windows", command=self.tile_windows).grid(
            row=0, column=2, sticky="ew", padx=4)
        GlowButton(trow, text="Free memory", command=self.free_memory_now).grid(
            row=0, column=3, sticky="ew", padx=4)
        GlowButton(trow, text="Check logins", command=self.check_logins).grid(
            row=0, column=4, sticky="ew", padx=(4, 0))
        card = Card(page, bg=SURFACE2)
        card.grid(row=14, column=0, sticky="ew", padx=18, pady=(10, 18))
        box = card.body
        box.columnconfigure(1, weight=1)
        edge = find_edge()
        for index, (title, value, color) in enumerate((
                ("Data", DATA_DIR, MUTED),
                ("Browser", "Microsoft Edge" if edge else "Edge not found - install it", GREEN if edge else DANGER),
                ("Version", f"{APP_NAME} {APP_VERSION}", MUTED))):
            pad = (12 if index == 0 else 4, 12 if index == 2 else 0)
            tk.Label(box, text=title, bg=SURFACE2, fg=FG, font=FONT_SMALL).grid(
                row=index, column=0, sticky="nw", padx=(14, 14), pady=pad)
            tk.Label(box, text=value, bg=SURFACE2, fg=color, font=FONT_MONO if index == 0 else FONT_SMALL,
                     justify="left", anchor="w", wraplength=520).grid(row=index, column=1, sticky="w", pady=pad)

    # --- profile pictures ---
    @staticmethod
    def _fetch_avatars(ids):
        """{user id: PNG bytes} of the Roblox headshots (60 x 60). Missing ones are simply left out."""
        out = {}

        def chunk_urls(chunk):
            try:
                r = requests.get("https://thumbnails.roblox.com/v1/users/avatar-headshot",
                                 params={"userIds": ",".join(map(str, chunk)), "size": "60x60", "format": "Png"},
                                 timeout=15)
                return [(d["targetId"], d["imageUrl"]) for d in r.json().get("data", []) if d.get("imageUrl")]
            except Exception:
                return []

        def get(item):
            try:
                resp = requests.get(item[1], timeout=15)
                return item[0], resp.content if resp.status_code == 200 else None
            except Exception:
                return item[0], None
        urls = {}
        with ThreadPoolExecutor(max_workers=4) as ex:
            for pairs in ex.map(chunk_urls, [ids[i:i + 100] for i in range(0, len(ids), 100)]):
                urls.update(pairs)
            for uid, data in ex.map(get, urls.items()):
                if data:
                    out[uid] = data
        return out

    def _start_avatar_load(self):
        """Shows the real Roblox profile picture of every logged-in account (cached on disk, refreshed per start)."""
        if self.closing or self._avatar_busy or time.time() - self._avatar_try < 45:
            return
        todo = {a["name"]: int(a["id"]) for a in self.accounts if a.get("id")
                and (self._avatar_shown.get(a["name"]) != int(a["id"]) or int(a["id"]) not in self._avatar_fresh)}
        if not todo:
            return
        self._avatar_busy, self._avatar_try = True, time.time()
        folder = os.path.join(DATA_DIR, "avatars")

        def post(found, fresh):
            if not self.closing:
                try:
                    self.after(0, lambda: self._apply_avatars(found, fresh))
                except (tk.TclError, RuntimeError):
                    pass

        def work():
            try:
                os.makedirs(folder, exist_ok=True)
                cached = {}
                for name, uid in todo.items():
                    path = os.path.join(folder, f"{uid}.png")
                    if self._avatar_shown.get(name) != uid and os.path.isfile(path):
                        with open(path, "rb") as fh:
                            cached[name] = (uid, fh.read())
                if cached:
                    post(cached, False)
                data = self._fetch_avatars(sorted(set(todo.values())))
                fresh = {}
                for name, uid in todo.items():
                    if uid in data:
                        fresh[name] = (uid, data[uid])
                        try:
                            with open(os.path.join(folder, f"{uid}.png"), "wb") as fh:
                                fh.write(data[uid])
                        except OSError:
                            pass
                if fresh:
                    post(fresh, True)
            except Exception:
                pass
            finally:
                self._avatar_busy = False
        threading.Thread(target=work, daemon=True, name="Multi-LauncherAvatars").start()

    def _apply_avatars(self, found, fresh):
        for name, (uid, data) in found.items():
            self.alist.set_avatar(name, base64.b64encode(data).decode("ascii"))
            self._avatar_shown[name] = uid
            if fresh:
                self._avatar_fresh.add(uid)

    # --- right-click menu and shortcuts ---
    def _account_menu(self, name, x, y):
        acc = next((a for a in self.accounts if a["name"] == name), None)
        if not acc:
            return
        menu = tk.Menu(self, tearoff=0, bg=SURFACE2, fg=FG, activebackground="#ffffff", activeforeground="#000000",
                       bd=0, relief="flat", font=FONT)
        if acc.get("id"):
            menu.add_command(label="Open profile in Edge", command=lambda: self._open_profile(acc))
        menu.add_command(label="Rocket off" if self._boosted(name) else "Rocket on",
                         command=lambda: self.toggle_boost(name))
        menu.add_command(label="Auto-relaunch off" if name in self.relaunch_on else "Auto-relaunch on",
                         command=lambda: self.toggle_relaunch(name))
        menu.add_command(label="Check login", command=lambda: self.check_logins({name}))
        menu.add_command(label="Copy username", command=lambda: (self.clipboard_clear(), self.clipboard_append(name)))
        menu.add_command(label="Select only this", command=lambda: (
            self.checked.clear(), self.checked.add(name), self._update_status_rows()))
        try:
            menu.tk_popup(x, y)
        finally:
            menu.grab_release()

    def _open_profile(self, acc):
        if not open_in_edge(f"https://www.roblox.com/users/{int(acc['id'])}/profile"):
            self.toast("Microsoft Edge was not found", bad=True)

    def _bind_shortcuts(self):
        def typing(event):
            return isinstance(event.widget, (tk.Entry, tk.Text, ttk.Entry))

        def select_all_key(event):
            if typing(event):
                return None
            self.select_all()
            return "break"

        def launch_key(_event):
            if self.btn_launch.cget("state") == "normal" and self.btn_launch._command:
                self.btn_launch._command()
            return "break"
        self.bind_all("<Control-a>", select_all_key)
        self.bind_all("<Control-Return>", launch_key)
        self.bind_all("<Control-f>", lambda _e: (self.show_page("fleet"), self.e_search.focus_set(), "break")[2])
        for number, (key, *_rest) in enumerate(self._PAGES, 1):
            self.bind_all(f"<Control-Key-{number}>", lambda _e, k=key: self.show_page(k))

    # --- rocket (per-account performance), multi-instance, tools ---
    def toggle_boost(self, name):
        if name in self.perf_off:
            self.perf_off.discard(name)
        else:
            self.perf_off.add(name)
        self._persist_settings()
        self.alist.refresh(self.accounts)
        on = self._boosted(name)
        if on and name in self.tracked and not self.tracked[name].get("stopped"):
            self._after_client_started(self.tracked[name]["pid"], name)
        self.toast(f"{name}: performance mode {'on' if on else 'off'} (graphics apply at next start)")

    # --- mute (live, all running clients) ---
    def toggle_mute_clients(self):
        self.mute_clients.set(not self.mute_clients.get())

    def _on_mute_changed(self):
        muted = bool(self.mute_clients.get())
        self._persist_settings()
        count = set_clients_muted(muted)
        if count is None:
            self.toast("Mute saved - install pycaw for live muting: pip install pycaw comtypes", bad=True)
        elif muted:
            self.toast(f"Muted {count} client(s) - new clients are muted automatically" if count else
                       "Mute on - clients will be silent")
        else:
            self.toast("Sound on")

    def _mute_loop(self):
        """While muted, mute clients that were started after the button was pressed."""
        if getattr(self, "closing", False):
            return
        try:
            if self.mute_clients.get():
                set_clients_muted(True)
        except Exception:
            pass
        self.after(3000, self._mute_loop)

    def boost_selected(self):
        names = [a["name"] for a in self._selected()]
        if not names:
            self.toast("Select accounts first", bad=True)
            return
        turn_on = any(n in self.perf_off for n in names)
        for n in names:
            if turn_on:
                self.perf_off.discard(n)
            else:
                self.perf_off.add(n)
        self._persist_settings()
        self.alist.refresh(self.accounts)
        self.toast(f"Performance mode {'on' if turn_on else 'off'} for {len(names)} account(s)")

    def _apply_speed(self, accounts=None):
        """Set the pauses and waits for the chosen launch speed. 'Smart' decides from the PC and the connection."""
        global LAUNCH_PAUSE, STABLE_SECONDS, WAIT_PER_TRY
        if not hasattr(self, "_speed_choice"):
            self._speed_choice = self.launch_speed.get()
        key = self._speed_choice
        if key == "smart":
            key, why = smart_speed(accounts or 1, self.net["state"], memory_status()[1], os.cpu_count() or 4)
            if accounts is not None:
                self.log(f"Smart launch speed: {key.capitalize()} ({why}).")
        LAUNCH_PAUSE, STABLE_SECONDS = {"slow": (6.0, 25), "safe": (3.0, 12), "fast": (1.0, 6), "instant": (0.4, 4)}.get(
            key, (1.0, 6))
        self._speed_key = key
        WAIT_PER_TRY = 70 if key == "slow" else 35

    def _on_speed_changed(self):
        self._speed_choice = self.launch_speed.get()
        self._apply_speed()
        self._persist_settings()
        if hasattr(self, "speed_desc"):
            self.speed_desc.set(self._type_text("speed"))
        self.toast(f"Launch speed: {self.launch_speed.get()}")

    # ---------- internet / Roblox reachability ----------
    def _net_hint(self, refresh=False):
        """Short sentence on whether the connection could be the reason for a problem ('' when it looks fine)."""
        if refresh:
            self._check_net_now()
        return NET_TEXT.get(self.net["state"], ("", ""))[1]

    def _check_net_now(self):
        state, ms = check_network()
        previous = self.net["state"]
        self.net.update(state=state, ms=ms)
        if state != previous:
            title, hint = NET_TEXT[state]
            try:
                if state == "ok":
                    self.log("Connection is back.")
                    self.after(0, lambda: self.toast("Connection is back"))
                else:
                    self.log(f"{title}. {hint}")
                    self.after(0, lambda: self.toast(title, bad=True))
                self.after(0, self._update_net_badge)
            except (tk.TclError, RuntimeError):
                pass
        return state

    def _update_net_badge(self):
        badge = getattr(self, "net_badge", None)
        if badge is None:
            return
        state, ms = self.net["state"], self.net["ms"]
        title = NET_TEXT[state][0]
        if state == "slow":
            title += f" ({ms / 1000:.1f} s)"
        if state == "ok":
            badge.config(text="")
        else:
            badge.config(text="\u25cf  " + title, fg=DANGER if state in ("offline", "roblox") else AMBER)

    def _net_loop(self):
        while not self._shutdown_event.wait(12 if self.net["state"] != "ok" else 25):
            try:
                self._check_net_now()
            except Exception:
                pass

    def _update_multi_badge(self):
        badge = getattr(self, "multi_badge", None)
        if badge is None:
            return
        if MULTI["ok"]:
            badge.config(text="\u25cf  Multi-instance ready", fg=GREEN, cursor="arrow")
        else:
            badge.config(text="\u25cf  Multi-instance blocked - click to fix", fg=DANGER, cursor="hand2")

    def _report_multi_instance(self):
        if MULTI["ok"]:
            self.log("Multi-instance ready: several Roblox clients can run side by side.")
        else:
            self.log(f"Multi-instance is blocked: {MULTI['note']}.")
        self._update_multi_badge()

    def fix_multi_instance(self):
        """The badge / button: close every Roblox client, take over the single-instance lock and say what happened."""
        if getattr(self, "_fixing_multi", False):
            return
        self._fixing_multi = True
        self.toast("Closing Roblox and taking over multi-instance ...")
        self.log("Closing all Roblox clients to fix multi-instance ...")
        for info in self.tracked.values():
            info["stopped"], info["state_text"] = True, "Closed to fix multi-instance"
        self._notify_state_changed()

        def work():
            try:
                ok = repair_multi_instance()
            except Exception as exc:
                ok = False
                self.log(f"Multi-instance fix failed: {exc}")

            def done():
                self._fixing_multi = False
                self._report_multi_instance()
                self._notify_state_changed()
                self.toast("Multi-instance ready" if ok else "Still blocked: " + MULTI["note"], bad=not ok)
            try:
                self.after(0, done)
            except (tk.TclError, RuntimeError):
                self._fixing_multi = False
        threading.Thread(target=work, daemon=True, name="FixMulti").start()

    def _on_auto_fix(self):
        self._auto_fix_on = bool(self.auto_fix.get())
        self._persist_settings()
        self.toast("Auto-fix " + ("on" if self._auto_fix_on else "off"))

    def _autofix_quick(self):
        """Before a launch (Auto-fix on): the cheap repairs that never disturb running clients."""
        try:
            n = repair_roblox_settings()
            if n:
                self.log(f"Auto-fix: repaired {n} damaged Roblox settings file(s).")
            free = memory_status()[1]
            if free and free < 1.5:
                self.log(f"Auto-fix: only {free:.1f} GB memory is free - close other programs or use a slower launch speed.")
        except Exception:
            pass

    def fix_everything(self):
        """Every repair in one go, with progress. Closes Roblox when that is needed for multi-instance."""
        def work():
            steps = [
                ("Checking the connection", self._fix_net),
                ("Repairing Roblox settings", self._fix_settings),
                ("Fixing multi-instance", self._fix_multi_quiet),
                ("Closing leftover Edge windows", self._fix_edge),
                ("Checking the clock", self._fix_clock),
                ("Clearing Roblox leftovers", self._fix_cache),
                ("Checking memory", self._fix_memory),
                ("Checking the saved logins", self._fix_logins),
            ]
            self._prog_start("Fixing", len(steps))
            fixed = 0
            try:
                for title, fn in steps:
                    if self._shutdown_event.is_set() or self._action_cancel_event.is_set():
                        break
                    self._prog_stage("", title, 0.5)
                    try:
                        result = fn()
                    except Exception as exc:
                        result = f"skipped ({str(exc)[:80]})"
                    if result:
                        fixed += 1
                        self.log(f"Fix: {title} - {result}")
                    self._prog_account_done(True)
            finally:
                self._prog_end()
            self.log("Fix everything: nothing needed fixing." if not fixed else f"Fix everything: {fixed} thing(s) handled.")
            try:
                self.after(0, lambda: self.toast("Everything is in order" if not fixed else f"{fixed} thing(s) fixed"))
            except (tk.TclError, RuntimeError):
                pass
        self._submit("Fix everything", "FIXING", work)

    def _fix_net(self):
        return self._net_hint(True) if self._check_net_now() != "ok" else ""

    def _fix_settings(self):
        n = repair_roblox_settings()
        return f"repaired {n} damaged settings file(s)" if n else ""

    def _fix_multi_quiet(self):
        if MULTI["ok"] and _mutex_handle:
            return ""
        for info in self.tracked.values():
            info["stopped"], info["state_text"] = True, "Closed to fix multi-instance"
        ok = repair_multi_instance()
        try:
            self.after(0, self._update_multi_badge)
            self.after(0, self._notify_state_changed)
        except (tk.TclError, RuntimeError):
            pass
        return "multi-instance ready" if ok else "still blocked: " + MULTI["note"]

    def _fix_edge(self):
        if self.login_lock.locked():
            return ""
        kill_edge_tree(None)
        return ""

    def _fix_clock(self):
        skew = clock_skew_seconds()
        if skew is None or abs(skew) <= 90:
            return ""
        ok = sync_clock()
        return (f"the clock was off by {int(abs(skew))} s and is synced now" if ok else
                f"the clock is off by {int(abs(skew))} s - turn on automatic time in Windows (administrator rights are needed to sync it from here)")

    def _fix_cache(self):
        count, size = clear_roblox_cache()
        return f"removed {count} file(s), {size / 1048576:.1f} MB" if count else ""

    def _fix_memory(self):
        free = memory_status()[1]
        return f"only {free:.1f} GB memory is free - close other programs or use a slower launch speed" if free and free < 1.5 else ""

    def _fix_logins(self):
        accs = [a for a in self.accounts if a.get("cookie") or a.get("password")]
        if not accs:
            return ""
        sessions = self._sessions_for(accs, allow_login=True)
        self._sync_cookies()
        bad = [a["name"] for a, x in zip(accs, sessions) if not x]
        return f"login still missing for {', '.join(bad)}" if bad else ""

    def tile_windows(self, quiet=False):
        pids = [i["pid"] for i in self.tracked.values() if not i.get("stopped")]
        if not pids:
            if not quiet:
                self.toast("No running clients", bad=True)
            return
        count = tile_roblox_windows(pids, tiny=bool(self.tiny_windows.get()))
        if count or not quiet:
            self.toast(f"Arranged {count} window(s)" if count else "No Roblox windows found", bad=not count)

    def check_logins(self, names=None):
        """Test the saved login of every account (or of the given ones) and say what is wrong."""
        targets = [a for a in self.accounts if names is None or a["name"] in names]
        if not targets:
            self.toast("No accounts to check", bad=True)
            return
        self.toast(f"Checking {len(targets)} login(s) ...")

        def work():
            good, problems = 0, 0
            for acc in targets:
                name = acc["name"]
                cookie = decrypt(acc.get("cookie", ""))
                if not cookie:
                    self.login_state[name] = "none"
                    self.log(f"{name}: no login saved - use 'Log in again'.")
                    problems += 1
                    continue
                session = RobloxSession(cookie)
                me = session.me(retries=2)
                if me and me.get("name", "").lower() == name.lower():
                    acc["id"], acc["display"] = me["id"], me.get("displayName", me.get("name", ""))
                    self._remember_session(name, session)
                    self.login_state[name] = "valid"
                    self.log(f"{name}: login works.")
                    good += 1
                elif me:
                    self.login_state[name] = "expired"
                    self.log(f"{name}: saved cookie belongs to another account - use 'Log in again'.")
                    problems += 1
                elif session.last_auth_state == "invalid":
                    self.login_state[name] = "expired"
                    self.log(f"{name}: login expired - use 'Log in again'.")
                    problems += 1
                else:
                    self.login_state[name] = "unknown"
                    self.log(f"{name}: could not check the login right now. {self._net_hint(True)}".strip())
                    problems += 1
            self._save()
            try:
                self.after(0, self._refresh_list)
                self.after(0, lambda: self.toast(f"{good} login(s) work" + (f", {problems} need attention" if problems else ""),
                                                 bad=bool(problems)))
            except (tk.TclError, RuntimeError):
                pass
        threading.Thread(target=work, daemon=True, name="CheckLogins").start()

    def _on_login_mode(self):
        mode = self.login_mode.get()
        if mode not in LOGIN_PROFILES:
            return
        self._login_choice = mode
        LOGIN_MODE["mode"] = "normal" if mode == "smart" else mode
        if hasattr(self, "login_desc"):
            self.login_desc.set(self._type_text("login"))
        self._persist_settings()
        self.toast(f"Login method: {mode.capitalize()}")

    def _relaunch_wanted(self, name):
        return name in self.relaunch_on

    def toggle_relaunch(self, name, state=None, quiet=False):
        """Automatic relaunch for one account: when its client closes or leaves the game it is started again.
        Closing it with Stop / Stop all / Remove ends it for good."""
        want = (name not in self.relaunch_on) if state is None else bool(state)
        if want:
            self.relaunch_on.add(name)
            held = self.tracked.get(name)
            if held and held.get("stopped") and not held.get("restarting"):
                held["stopped"], held["next_try"], held["errseen"] = False, 0, 0  # closed earlier: comes back now
        else:
            self.relaunch_on.discard(name)
        self._persist_settings()
        self.alist.refresh(self.accounts)
        self._monitor_event.set()
        if not quiet:
            self.toast(f"{name}: auto-relaunch {'on' if want else 'off'}")

    def relaunch_selected(self):
        sel = [a["name"] for a in self._selected()]
        if not sel:
            self.toast("Select accounts first", bad=True)
            return
        want = not all(n in self.relaunch_on for n in sel)
        for n in sel:
            self.toggle_relaunch(n, want, quiet=True)
        self.toast(f"Auto-relaunch {'on' if want else 'off'} for {len(sel)} account(s)")

    def _on_flag_pack(self):
        self._persist_settings()
        on = [FLAG_PACKS[k][0] for k, v in self.flag_packs.items() if v.get()]
        self.toast("Flag packs: " + (", ".join(on) if on else "none") + " (next client start)")

    def free_memory_now(self):
        pids = [i["pid"] for i in self.tracked.values() if not i.get("stopped")]
        if not pids:
            self.toast("No running clients", bad=True)
            return

        def work():
            done = free_memory(pids)
            try:
                self.after(0, lambda: self.toast(f"Trimmed memory of {done} client(s)"))
            except (tk.TclError, RuntimeError):
                pass
        threading.Thread(target=work, daemon=True, name="Trim").start()

    def _on_window_option_silent(self):
        try:
            self.attributes("-topmost", bool(self.always_on_top.get()))
        except tk.TclError:
            pass

    def _on_window_option(self):
        try:
            self.attributes("-topmost", bool(self.always_on_top.get()))
        except tk.TclError:
            pass
        self._persist_settings()

    def apply_preset(self, key):
        if key == "potato":
            self.performance_mode.set(True); self.lean_clients.set(True); self.fps_cap.set("15")
            self.perf_off.clear()
            self._refresh_list()
        elif key == "balanced":
            self.performance_mode.set(False); self.lean_clients.set(True); self.fps_cap.set("30")
        else:
            self.performance_mode.set(False); self.lean_clients.set(False); self.fps_cap.set("0")
        self._on_optimization_changed()
        self.toast({"potato": "Potato preset: rockets on for all accounts",
                    "balanced": "Balanced preset", "off": "Optimizations off"}[key])

    def clear_cache(self):
        def work():
            count, size = clear_roblox_cache()
            try:
                self.after(0, lambda: self.toast(f"Removed {count} file(s), {size / 1048576:.1f} MB"))
            except (tk.TclError, RuntimeError):
                pass
        threading.Thread(target=work, daemon=True, name="Multi-LauncherCache").start()

    def save_flags(self):
        ok, message = save_custom_flags(self.e_flags.get("1.0", "end-1c"))
        self.toast(("Saved: " if ok else "Not saved: ") + message + (" (applies at next start)" if ok else ""), bad=not ok)

    def toast(self, text, bad=False):
        """Small message that slides up from the bottom and fades away again."""
        try:
            label = getattr(self, "_toast", None)
            if label is None:
                label = self._toast = tk.Label(self, font=FONT_BOLD, padx=18, pady=10)
            job = getattr(self, "_toast_job", None)
            if job:
                self.after_cancel(job)
            label.configure(text=text, bg=DANGER if bad else "#ffffff", fg="#000000")
            label.place(relx=0.5, rely=1.0, anchor="s", y=40)
            label.lift()

            def rise(v):
                label.place_configure(y=40 - 90 * v)
            Anim.run(label, 240, rise, key="toast")

            def leave():
                def sink(v):
                    label.place_configure(y=-50 + 90 * v)
                Anim.run(label, 200, sink, done=label.place_forget, key="toast")
            self._toast_job = self.after(2600, leave)
        except tk.TclError:
            pass

    # --- Log page ---
    def _build_log_page(self, page):
        page.columnconfigure(0, weight=1)
        page.rowconfigure(1, weight=1)
        head = tk.Frame(page, bg=SURFACE)
        head.grid(row=0, column=0, sticky="ew", padx=18, pady=(16, 8))
        head.columnconfigure(0, weight=1)
        tk.Label(head, text="Activity", bg=SURFACE, fg=FG, font=FONT_H2).grid(row=0, column=0, sticky="w")
        GlowButton(head, text="Clear", command=self._clear_log, small=True).grid(row=0, column=1)
        wrap = tk.Frame(page, bg=SURFACE)
        wrap.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 18))
        wrap.columnconfigure(0, weight=1)
        wrap.rowconfigure(0, weight=1)
        self.log_box = tk.Text(wrap, bg=INPUT, fg=FG, font=FONT_MONO, relief="flat", bd=0, wrap="word",
                               state="disabled", highlightthickness=1, highlightbackground=BORDER,
                               padx=10, pady=8, selectbackground=ACCENT_DARK, cursor="arrow")
        log_scroll = ttk.Scrollbar(wrap, orient="vertical", style="Slim.Vertical.TScrollbar",
                                   command=self.log_box.yview)
        self.log_box.configure(yscrollcommand=log_scroll.set)
        self.log_box.grid(row=0, column=0, sticky="nsew")
        log_scroll.grid(row=0, column=1, sticky="ns", padx=(4, 0))
        indent = tkfont.Font(font=FONT_MONO).measure("00:00:00  ATTENTION   ")
        self.log_box.tag_configure("line", lmargin1=0, lmargin2=indent)
        self.log_box.tag_configure("stamp", foreground=DIM)
        self.log_box.tag_configure("ok", foreground=GREEN)
        self.log_box.tag_configure("bad", foreground=DANGER)
        self.log_box.tag_configure("warn", foreground=AMBER)
        self.log_box.tag_configure("info", foreground=ACCENT_LIGHT)

    _LOG_TAGS = {"ATTENTION": "bad", "READY": "ok", "WAITING": "warn", "STOPPING": "warn", "QUEUED": "warn"}

    def _append_log(self, kind, text):
        box = getattr(self, "log_box", None)
        if box is None:
            return
        try:
            box.configure(state="normal")
            box.insert("end", time.strftime("%H:%M:%S") + "  ", ("stamp", "line"))
            box.insert("end", f"{kind:<10} ", (self._LOG_TAGS.get(kind, "info"), "line"))
            box.insert("end", text + "\n", "line")
            lines = int(box.index("end-1c").split(".")[0])
            if lines > 500:
                box.delete("1.0", f"{lines - 500 + 1}.0")
            box.see("end")
            box.configure(state="disabled")
        except tk.TclError:
            pass

    def _clear_log(self):
        try:
            self.log_box.configure(state="normal")
            self.log_box.delete("1.0", "end")
            self.log_box.configure(state="disabled")
        except tk.TclError:
            pass

    # --- status dock (bottom) ---
    def _build_dock(self, main):
        card = Card(main, bg=SURFACE)
        card.grid(row=2, column=0, sticky="ew", pady=(12, 18))
        bar = card.body
        bar.columnconfigure(0, weight=1)
        self.activity_state = tk.StringVar(value="READY")
        self.activity_title = tk.StringVar(value="Ready")
        self.activity_detail = tk.StringVar(value="")
        self.activity_queue = tk.StringVar(value="")
        self.activity_problem = tk.StringVar(value="")
        self.activity_chip = tk.Label(bar, textvariable=self.activity_state, bg=SURFACE3, fg="#ffffff")  # not shown
        top = tk.Frame(bar, bg=SURFACE)
        top.grid(row=0, column=0, sticky="ew", padx=18, pady=(12, 0))
        top.columnconfigure(0, weight=1)
        tk.Label(top, textvariable=self.activity_title, bg=SURFACE, fg=FG, font=FONT_H2, anchor="w").grid(
            row=0, column=0, sticky="w")
        tk.Label(top, textvariable=self.activity_queue, bg=SURFACE, fg=MUTED, font=FONT_SMALL).grid(
            row=0, column=1, sticky="e", padx=(8, 12))
        self.activity_progress = GlowProgress(top, bg=SURFACE, width=170, height=8)
        self.activity_progress.grid(row=0, column=2)
        self._progress_mode = "idle"
        self.activity_detail_label = tk.Label(bar, textvariable=self.activity_detail, bg=SURFACE, fg=MUTED,
                                              font=FONT, anchor="w", justify="left", wraplength=760)
        self.activity_detail_label.grid(row=1, column=0, sticky="ew", padx=18, pady=(2, 12))
        self.activity_problem_label = tk.Label(bar, textvariable=self.activity_problem, bg=SURFACE, fg=DANGER,
                                               font=FONT, anchor="w", justify="left", wraplength=760)
        self.activity_problem_label.grid(row=2, column=0, sticky="ew", padx=18, pady=(0, 12))
        self.activity_problem_label.grid_remove()

        def _fit(event):
            width = max(300, event.width - 60)
            self.activity_detail_label.config(wraplength=width)
            self.activity_problem_label.config(wraplength=width)
        bar.bind("<Configure>", _fit)

    def _on_close(self):
        try:
            self._sync_cookies()
        except Exception:
            pass
        self.closing = True
        self._action_cancel_event.set()
        self._launch_cancel_event.set()
        self._shutdown_event.set()
        self._monitor_event.set()
        try:
            self.destroy()
        except tk.TclError:
            pass

    def _persist_settings(self):
        self.settings["performance_mode"] = bool(self.performance_mode.get())
        self.settings["extreme_save_mode"] = bool(self.extreme_save_mode.get())
        self.settings["auto_recovery"] = bool(self.auto_recovery.get())
        self.settings["lean_clients"] = bool(self.lean_clients.get())
        self.settings["launch_speed"] = self.launch_speed.get()
        self.settings["mute_clients"] = bool(self.mute_clients.get())
        self.settings["auto_tile"] = bool(self.auto_tile.get())
        self.settings["tiny_windows"] = bool(self.tiny_windows.get())
        self.settings["auto_fix"] = bool(self.auto_fix.get())
        self.settings["recent_games"] = [{"id": int(g["id"]), "name": str(g.get("name", ""))} for g in self.recent_games][:8]
        self.settings["login_mode"] = self.login_mode.get() if self.login_mode.get() in LOGIN_PROFILES else "safe"
        self.settings["flag_packs"] = [k for k, v in self.flag_packs.items() if v.get()]
        self.settings["relaunch_on"] = sorted(self.relaunch_on)
        self.settings["always_on_top"] = bool(self.always_on_top.get())
        self.settings["perf_off"] = sorted(self.perf_off)
        try:
            self.settings["fps_cap"] = int(self.fps_cap.get())
        except ValueError:
            self.settings["fps_cap"] = 30
        self.settings["specific_users"] = list(self.specific_users)
        try:
            save_settings(self.settings)
            return True
        except OSError as exc:
            self.log(f"Could not save settings: {exc}")
            return False

    def _on_optimization_changed(self):
        self._persist_settings()
        self._monitor_event.set()
        self.log(
            "Optimization settings updated: "
            + ("Quality Performance Mode on; " if self.settings["performance_mode"] else "Quality Performance Mode off; ")
            + ("automatic recovery on; " if self.settings["auto_recovery"] else "automatic recovery off; ")
            + (f"lean clients on ({self.settings['fps_cap']} fps cap)." if self.settings["lean_clients"] else "lean clients off.")
        )

    def _monitor_interval(self):
        if self.extreme_save_mode.get():
            return 10.0
        if self.performance_mode.get():
            return 6.0
        return 4.0

    def _presence_interval(self):
        if self.extreme_save_mode.get():
            return 60.0
        if self.performance_mode.get():
            return 40.0
        return 25.0

    def _launch_probe_interval(self):
        if os.name == "nt":
            return 0.3
        if self.extreme_save_mode.get():
            return 2.0
        if self.performance_mode.get():
            return 1.25
        return 0.75

    # ---------- Helpers ----------
    @staticmethod
    def _activity_kind(message):
        text = str(message).lower()
        if text.startswith(("done:", "ready.", "ready ")) or "ready for new actions" in text:
            return "READY"
        if any(word in text for word in ("error", "failed", "could not", "warning", "rejected", "problem",
                                         "crashed", "not responding", "unwanted tab", "left roblox.com")):
            return "ATTENTION"
        if "rate limit" in text or "slow down" in text:
            return "WAITING"
        if "waiting in line" in text:
            return "QUEUED"
        if any(word in text for word in ("stopping", "cancelled", "stopped", "emergency stop")):
            return "STOPPING"
        if "complete" in text or "finished" in text:
            return "READY"
        if any(word in text for word in ("imported", "migrat", "moving", "moved")):
            return "MOVING"
        if "add-on" in text or "extension" in text:
            return "ADD-ON"
        if any(word in text for word in ("installing", "installed")):
            return "INSTALLING"
        if "updated the launcher" in text or "launcher update" in text:
            return "UPDATING"
        if "joining" in text or "joinable game" in text:
            return "JOINING"
        if "follow" in text:
            return "FOLLOWING"
        if "friends" in text:
            return "FRIENDS"
        if any(word in text for word in ("outfit", "equipp", "marketplace", "item(s) to get", "got '")):
            return "OUTFIT"
        if any(word in text for word in ("display name", "profile bio", "updating", "bio ")):
            return "UPDATING"
        if any(word in text for word in ("launch", "restarting", "running", "start method")):
            return "LAUNCHING"
        if any(word in text for word in ("edge", "browser", "login", "sign-in", "signed in", "checking saved")):
            return "SIGNING IN"
        return "WORKING"

    _CHIP_COLORS = {"READY": "#2b2b2e", "ATTENTION": "#b3261e", "STOPPING": "#8a6100", "QUEUED": "#34495e",
                    "WAITING": "#8a6100"}
    _IDLE_TITLES = {
        "READY": "Ready", "ATTENTION": "Needs attention", "STOPPING": "Stopping", "QUEUED": "Waiting in line", "WAITING": "Waiting for Roblox",
        "JOINING": "Joining a game", "LAUNCHING": "Launching clients", "SIGNING IN": "Signing in",
        "MOVING": "Moving your data", "UPDATING": "Updating", "INSTALLING": "Installing", "ADD-ON": "Edge add-on",
        "FRIENDS": "Friends", "FOLLOWING": "Following", "OUTFIT": "Outfit", "WORKING": "Working",
    }

    @staticmethod
    def _friendly(text):
        """Shorter, cleaner wording for the status bar: 'raheem: got 'Shirt'.' -> 'raheem · got 'Shirt'.'"""
        text = str(text).strip()
        match = re.match(r"^([\w.\-]{2,24}): (.+)$", text)
        if match and match.group(1).lower() not in ("done", "warning", "error", "ready", "outfit", "bio"):
            text = f"{match.group(1)} · {match.group(2)}"
        return (text[:1].upper() + text[1:])[:260]

    def _set_progress_mode(self, mode, total=0, done=0):
        prog = self.activity_progress
        if mode == "steps":
            prog.set_steps(total, done)
        elif mode == "busy":
            prog.set_busy()
        else:
            prog.set_idle()
        self._progress_mode = mode

    def _update_orb(self, chip):
        if not hasattr(self, "nav"):
            return
        if chip == "READY":
            self.nav.set_orb(GREEN, False)
        elif chip == "ATTENTION":
            self.nav.set_orb(DANGER, True)
        elif chip in ("WAITING", "STOPPING", "QUEUED"):
            self.nav.set_orb(AMBER, True)
        else:
            self.nav.set_orb(ACCENT, True)

    def _render_status(self):
        """Draw the status bar from the running tool, the waiting line and the latest message (UI thread)."""
        if self.closing or not hasattr(self, "activity_state"):
            return
        try:
            snap = self.jobs.snapshot()
            cur, waiting = snap["current"], snap["waiting"]
            kind, text = self._last_message
            if cur and self._status_job != cur["number"]:
                self._status_job = cur["number"]
                self._problems = []
                kind, text = cur["kind"], "Starting ..."
                self._last_message = (kind, text)
            if self._stopping:
                chip, title = "STOPPING", "Stopping everything"
            elif cur:
                chip, title = cur["kind"], cur["title"]
                if cur["total"]:
                    title += f"    {cur['done']}/{cur['total']}"
                if cur["started"]:
                    title += f"    {int(time.time() - cur['started'])} s"
            else:
                recent = (time.monotonic() - self._last_message_t) < 12
                if self.busy or self._prog_visible():
                    chip = kind if kind in self._IDLE_TITLES else "WORKING"
                elif recent and kind == "ATTENTION":
                    chip = "ATTENTION"
                else:
                    chip = "READY"
                title = self._IDLE_TITLES.get(chip, "Ready")
                if chip == "READY":
                    text = text if recent else "Nothing to do."
                    if time.monotonic() - self._last_message_t > 60:
                        self._problems = []
            self.activity_state.set(chip)
            self.activity_title.set(title)
            self.activity_detail.set(text or "Working ...")
            self.activity_chip.config(bg=self._CHIP_COLORS.get(chip, RED_DARK))
            self._update_orb(chip)
            if waiting:
                shown = ", ".join(waiting[:3]) + (f" +{len(waiting) - 3}" if len(waiting) > 3 else "")
                self.activity_queue.set(f"Next: {shown}")
            else:
                self.activity_queue.set("")
            if cur and cur["total"] and not self._stopping:
                self._set_progress_mode("steps", cur["total"], cur["done"])
            elif cur or self._stopping:
                self._set_progress_mode("busy")
            else:
                self._set_progress_mode("idle")
            if self._problems:
                extra = f"   (+{len(self._problems) - 1} more)" if len(self._problems) > 1 else ""
                self.activity_problem.set("\u26a0  " + self._problems[-1] + extra)
                self.activity_problem_label.grid()
            else:
                self.activity_problem.set("")
                self.activity_problem_label.grid_remove()
            if self._prog_visible():
                self._render_progress()
        except tk.TclError:
            pass

    def _jobs_changed(self):
        """Called from the waiting line (any thread): redraw and keep the elapsed time ticking."""
        if self.closing:
            return
        try:
            self.after(0, self._on_jobs_changed)
        except (tk.TclError, RuntimeError):
            pass

    def _on_jobs_changed(self):
        self._render_status()
        if self.jobs.busy() and not self._tick_scheduled:
            self._tick_scheduled = True
            self.after(1000, self._tick_status)

    def _tick_status(self):
        self._tick_scheduled = False
        if self.closing:
            return
        if self.jobs.busy():
            self._render_status()
            self._tick_scheduled = True
            self.after(1000, self._tick_status)

    def log(self, msg):
        if self.closing:
            return
        text = str(msg).replace("\n", " ").strip()
        kind = self._activity_kind(text)

        def _do():
            if self.closing or not hasattr(self, "activity_state"):
                return
            friendly = self._friendly(text)
            if kind == "ATTENTION":
                self._problems = (self._problems + [friendly])[-6:]
            self._last_message = (kind, friendly)
            self._last_message_t = time.monotonic()
            self.after(13000, self._render_status)
            self._append_log(kind, friendly)
            self._render_status()
        try:
            self.after(0, _do)
        except (tk.TclError, RuntimeError):
            pass
    def _status(self, acc):
        info = self.tracked.get(acc["name"])
        if info and not info.get("stopped"):
            if info.get("restarting"):
                return "Restarting ..."
            text = info.get("state_text") or "Running"
            mem = info.get("mem")
            return f"{text} \u00b7 {mem} MB (PID {info['pid']})" if mem else f"{text} (PID {info['pid']})"
        if info and info.get("stopped"):
            return f"Stopped - {info['state_text']}" if info.get("state_text") else "Stopped"
        state = self.login_state.get(acc["name"])
        if state == "checking":
            return "Checking cookies ..."
        if acc.get("cookie") and state in (None, "valid"):
            return "Ready"
        return "Need to login first"

    def _card_state(self, acc):
        """(status text, colour tag) for the account card."""
        status = re.sub(r"\s*\(PID \d+\)", "", self._status(acc))
        info = self.tracked.get(acc["name"])
        if info:
            if info.get("stopped"):
                tag = "idle"
            elif info.get("restarting") or info.get("state") in ("dialog", "lobby", "unknown"):
                tag = "warn"
            elif info.get("state") in ("error", "hung", "closed"):
                tag = "bad"
            else:
                tag = "run"
        else:
            state = self.login_state.get(acc["name"])
            if state == "checking":
                tag = "idle"
            elif acc.get("cookie") and state in (None, "valid"):
                tag = "ok"
            else:
                tag = "warn"
        return status, tag

    def _update_stats(self):
        label = getattr(self, "acc_count", None)
        if label is None:
            return
        if not self.accounts:
            label.config(text="")
            return
        tags = [self._card_state(a)[1] for a in self.accounts]
        names = {a["name"] for a in self.accounts}
        parts = [f"{len(self.accounts)} account" + ("" if len(self.accounts) == 1 else "s")]
        picked = len(self.checked & names)
        running = tags.count("run")
        alerts = tags.count("warn") + tags.count("bad")
        for count, word in ((picked, "selected"), (running, "running"), (alerts, "alerts")):
            if count:
                parts.append(f"{count} {word}" if word != "alerts" else f"{count} alert" + ("" if count == 1 else "s"))
        if len(parts) > 1:
            parts[0] = str(len(self.accounts))
        label.config(text=" \u00b7 ".join(parts))

    def _update_counts(self):
        self._update_stats()

    def _refresh_list(self):
        if self.closing:
            return
        self.alist.sync(self.accounts)
        self._update_counts()
        self._start_avatar_load()

    def _update_status_rows(self):
        if self.closing:
            return
        try:
            self.alist.refresh(self.accounts)
            self._update_stats()
            self._start_avatar_load()
        except tk.TclError:
            pass

    def _notify_state_changed(self, wake_monitor=True):
        if wake_monitor:
            self._monitor_event.set()
        if not self.closing:
            try:
                self.after(0, self._update_status_rows)
            except tk.TclError:
                pass

    def _toggle_account(self, name):
        if name in self.checked:
            self.checked.discard(name)
        else:
            self.checked.add(name)
        self.alist.refresh(self.accounts)
        self._update_stats()

    def select_all(self):
        self.checked = {a["name"] for a in self.accounts}
        self._refresh_list()

    def clear_all(self):
        self.checked.clear()
        self._refresh_list()

    def _selected(self):
        return [a for a in self.accounts if a["name"] in self.checked]

    def _save(self):
        try:
            save_accounts(self.accounts)
            return True
        except Exception as e:
            err = str(e)
            self.log(f"SAVING FAILED: {err}")
            self.after(0, lambda: messagebox.showerror("Saving failed", err))
            return False

    # ---------- Sessions ----------
    def _remember_session(self, name, session):
        with self._sessions_lock:
            self.session_cache[name.lower()] = session

    def _cached_session(self, name):
        with self._sessions_lock:
            session = self.session_cache.get(name.lower())
            if session is not None and getattr(session, "last_auth_state", "unknown") == "invalid":
                self.session_cache.pop(name.lower(), None)
                return None
            return session

    def _sessions_for(self, accs, cancel_event=None, allow_login=True, force_fresh=False, prompt_missing=True):
        """Reuse cached/DPAPI sessions; only open Edge for a genuinely expired or missing login."""
        if not accs:
            return []
        # Calls from tools such as account login and recovery do not always pass
        # their own event.  They must still honour the central emergency stop.
        cancel_event = cancel_event or self._job_cancel_any
        if cancel_event.is_set() or self._shutdown_event.is_set():
            return [None] * len(accs)

        def check(acc):
            cached = self._cached_session(acc["name"])
            if cached:
                return cached, "cached"

            stored_cookie = acc.get("cookie", "")
            cookie = decrypt(stored_cookie)
            if not cookie:
                return None, "unreadable" if stored_cookie else "missing"

            session = RobloxSession(cookie)
            me = session.me()
            if me:
                if me.get("name", "").lower() != acc["name"].lower():
                    return None, "wrong-account"
                acc["id"] = me["id"]
                acc["display"] = me.get("displayName", me.get("name", ""))
                self._remember_session(acc["name"], session)
                return session, "valid"

            if session.last_auth_state == "temporary":
                # Roblox may be rate-limiting or temporarily unreachable. Do not
                # destroy a good saved cookie or force the user through Edge.
                self._remember_session(acc["name"], session)
                return session, "temporary"
            return None, "expired"

        with ThreadPoolExecutor(max_workers=max(1, min(16, len(accs)))) as executor:
            checked = list(executor.map(check, accs))
        if cancel_event.is_set() or self._shutdown_event.is_set():
            return [None] * len(accs)
        sessions = [item[0] for item in checked]
        need = [(index, acc, checked[index][1])
                for index, (acc, session) in enumerate(zip(accs, sessions)) if session is None]

        if need and allow_login:
            with self.login_lock:
                still_need = []
                for index, acc, reason in need:
                    cached = self._cached_session(acc["name"])
                    if cached:
                        sessions[index] = cached
                        continue
                    cookie = decrypt(acc.get("cookie", ""))
                    if cookie:
                        retry_session = RobloxSession(cookie)
                        me = retry_session.me()
                        if me and me.get("name", "").lower() == acc["name"].lower():
                            acc["id"] = me["id"]
                            acc["display"] = me.get("displayName", me.get("name", ""))
                            self._remember_session(acc["name"], retry_session)
                            sessions[index] = retry_session
                            continue
                        if retry_session.last_auth_state == "temporary":
                            self._remember_session(acc["name"], retry_session)
                            sessions[index] = retry_session
                            continue
                    if reason == "unreadable":
                        self.log(f"{acc['name']}: saved sign-in could not be decrypted; a new login is required.")
                    elif reason == "wrong-account":
                        self.log(f"{acc['name']}: saved cookie belongs to a different account; please sign in again.")
                    still_need.append((index, acc))

                if still_need and not (cancel_event is not None and cancel_event.is_set()):
                    self._prog_stage("", f"signing in {len(still_need)} account(s) in Edge ({LOGIN_MODE['mode']} login)")
                    self.log(f"Login needed for {len(still_need)} account(s) - opening Edge ...")
                    if self._login_choice == "smart":
                        LOGIN_MODE["mode"], why = smart_login(len(still_need), self.net["state"], self._login_failures)
                        self.log(f"Smart login: {LOGIN_MODE['mode'].capitalize()} ({why}).")
                    # Prompt when the account has NEITHER a saved cookie NOR a
                    # saved password on disk (raw fields, not decrypted - so a
                    # DPAPI hiccup can't lie about what's stored). The dialog is
                    # suppressed for background-only callers that pass False.
                    ask_for = []
                    if prompt_missing:
                        ask_for = [acc for _, acc in still_need
                                   if not acc.get("password")
                                   and not acc.get("cookie")]
                    entered = (self._prompt_passwords_sync([a["name"] for a in ask_for])
                               if ask_for else {})
                    payload = []
                    skipped = set()
                    for _idx, acc in still_need:
                        pw = decrypt(acc.get("password", ""))
                        if not pw and acc in ask_for:
                            pw = entered.get(acc["name"], "")
                            if not pw:
                                self.log(f"{acc['name']}: no password entered - skipping login.")
                                skipped.add(acc["name"])
                                continue
                            acc["password"] = encrypt(pw)
                            self._save()
                        payload.append((acc, pw or ""))
                    still_need = [(i, a) for (i, a) in still_need if a["name"] not in skipped]
                    cookies = edge_login_many(
                        payload, self.log, cancel_event=cancel_event, force_fresh=force_fresh
                    ) if payload else {}
                    self._login_failures = 0 if all(a["name"] in cookies for _i, a in still_need) else self._login_failures + 1
                    changed = False
                    for index, acc in still_need:
                        if cancel_event is not None and cancel_event.is_set():
                            break
                        cookie = cookies.get(acc["name"])
                        if not cookie:
                            continue
                        new_session = RobloxSession(cookie)
                        me = new_session.me_after_login()
                        if me and me.get("name", "").lower() != acc["name"].lower():
                            self.log(f"{acc['name']}: Edge returned a different Roblox account; cookie not saved.")
                            continue
                        if new_session.last_auth_state == "invalid":
                            self.log(f"{acc['name']}: Roblox rejected the new session; please try signing in again.")
                            continue
                        acc["cookie"] = encrypt(cookie)
                        # Cookies-first: Passwort nach erstem erfolgreichem Login verwerfen.
                        if acc.pop("password", None) is not None:
                            self.log(f"{acc['name']}: password discarded - cookie login from now on.")
                        changed = True
                        if me:
                            acc["id"] = me["id"]
                            acc["display"] = me.get("displayName", me.get("name", ""))
                        self._remember_session(acc["name"], new_session)
                        sessions[index] = new_session
                        self.log(f"{acc['name']}: sign-in saved.")
                    if changed:
                        self._save()

        if not self.closing:
            try:
                self.after(0, self._refresh_list)
            except tk.TclError:
                pass
        for _acc, _sess in zip(accs, sessions):
            self.login_state[_acc["name"]] = "valid" if _sess else ((
                "unknown" if self.net["state"] in ("offline", "roblox") else "expired") if _acc.get("cookie") else "none")
        try:
            self._sync_cookies()
        except Exception:
            pass
        return sessions

    def _ensure_id(self, acc, sess):
        """Make sure acc['id'] / acc['display'] exist (needed for display name, friends, outfit)."""
        if acc.get("id"):
            return True
        try:
            me = sess.me()
        except Exception:
            me = None
        if me:
            acc["id"] = me["id"]
            acc["display"] = me.get("displayName", me.get("name", ""))
            self._save()
            return True
        return False

    def _warmup(self):
        """At start-up validate saved logins in the background so launching is instant (never opens Edge)."""
        try:
            accs = [a for a in self.accounts if a.get("cookie")]
            for a in accs:
                self.login_state[a["name"]] = "checking"
            if accs:
                self.after(0, self._refresh_list)
                sessions = self._sessions_for(accs, allow_login=False, prompt_missing=False)
                ready = sum(1 for x in sessions if x)
                bad = [a["name"] for a, x in zip(accs, sessions) if not x]
                if bad:
                    self.log(f"Saved logins loaded: {ready}/{len(accs)} ready. New login needed for {', '.join(bad)}. {self._net_hint(True)}".strip())
                else:
                    self.log(f"Saved logins loaded: all {ready} account(s) are ready to launch.")
                self.after(0, self._refresh_list)
        except Exception as exc:
            self.log(f"Login warm-up skipped: {exc}")

    def _precheck_clock(self):
        """A wrong PC clock breaks logins. Checked in the background (not on every start)."""
        if time.monotonic() - getattr(self, "_skew_checked", -1e9) < 600:
            return
        self._skew_checked = time.monotonic()
        skew = clock_skew_seconds()
        if skew is not None and abs(skew) > 90:
            if self._auto_fix_on and sync_clock():
                self.log("Auto-fix: the PC clock was off and has been synced.")
                return
            self.log(f"WARNING: your PC clock is off by about {int(abs(skew))} s. Roblox rejects logins "
                     "when the time is wrong (authentication error). Turn on automatic time in Windows "
                     "Settings > Time & language and click 'Sync now'.")

    def _precheck_net(self):
        if self._check_net_now() == "offline":
            self.log("No internet connection detected - trying anyway. Check your network if nothing starts.")

    def _warm_sessions(self, sessions):
        """Fetch the security token of every session at once so the launches do not wait for it one by one."""
        todo = [s_ for s_ in sessions if s_ is not None and not s_.csrf]
        if not todo:
            return

        def warm(sess):
            try:
                sess._refresh_csrf()
            except Exception:
                pass
        with ThreadPoolExecutor(max_workers=min(8, len(todo))) as ex:
            list(ex.map(warm, todo))

    def _cookie_loop(self):
        """Every few minutes: keep the saved logins alive, store a cookie Roblox has renewed and retry
        logins that could not be checked earlier (never opens Edge)."""
        while not self._shutdown_event.wait(480):
            try:
                if self.busy:
                    continue
                with self._sessions_lock:
                    live = list(self.session_cache.values())
                for sess in live:
                    sess.me(retries=1)
                self._sync_cookies()
                retry = [a for a in self.accounts if a.get("cookie") and self.login_state.get(a["name"]) in ("unknown", "expired")]
                if retry:
                    self._sessions_for(retry, allow_login=False, prompt_missing=False)
                    self._sync_cookies()
            except Exception:
                pass

    def _sync_cookies(self):
        """Roblox can rotate the login cookie: store the newest one so the next start stays instant."""
        changed = False
        with self._sessions_lock:
            items = list(self.session_cache.items())
        for key, sess in items:
            try:
                current = sess.s.cookies.get(".ROBLOSECURITY")
            except Exception:
                continue
            acc = next((a for a in self.accounts if a["name"].lower() == key), None)
            if not acc or not current or getattr(sess, "last_auth_state", "") != "authenticated":
                continue
            if decrypt(acc.get("cookie", "")) != current:
                acc["cookie"] = encrypt(current)
                changed = True
        if changed:
            self._save()

    @staticmethod
    def _is_challenge(detail):
        return "challenge" in str(detail).lower()

    _LIMIT_RE = re.compile(r"once every|7 days|cooldown|can only be changed|cannot change|can't change", re.I)

    @classmethod
    def _limit_reason(cls, status, detail):
        """A real change cooldown (for example 'once every 7 days'): the tool stops for that account.
        Plain rate limits are NOT stopped - they are waited out (see RateGate)."""
        text = str(detail or "")
        if cls._LIMIT_RE.search(text):
            return text[:140]
        return None

    @staticmethod
    def _is_rate_limit(status, detail):
        return status == 429 or bool(RATE_TEXT_RE.search(str(detail or "")))

    def _rate_wait(self, host, seconds=15):
        _RATE.hit(host, seconds)
        _RATE.wait(host)

    def _limit_hit(self, name):
        """True once (and forgets it) when this account stopped because of a limit - already reported."""
        with self._limit_lock:
            if name in self._limit_names:
                self._limit_names.discard(name)
                return True
        return False

    def _swallow_thread_error(self, args):
        """Keep worker thread crashes from surfacing as a crash dialog."""
        try:
            name = getattr(args.thread, "name", "worker")
            self.log(f"Background error ({name}): {args.exc_type.__name__}: {str(args.exc_value)[:160]}")
        except Exception:
            pass

    def _swallow_callback_error(self, exc, val, tb):
        """Handler for Tk's report_callback_exception. Never let a widget
        exception close the main window - only child dialogs close."""
        try:
            self.log(f"GUI error (ignored): {val.__class__.__name__}: {str(val)[:160]}")
        except Exception:
            pass
        # Close any orphan modal that may still be holding a grab, but keep
        # the main window alive.
        try:
            holder = self.grab_current()
            if holder is not None and holder is not self:
                try:
                    holder.grab_release()
                except tk.TclError:
                    pass
                try:
                    holder.destroy()
                except tk.TclError:
                    pass
        except tk.TclError:
            pass

    def _prompt_passwords_sync(self, names):
        """One modal dialog listing every account that needs a password.
        Usernames are shown locked, each row has its own masked password field.
        Returns {name: plaintext or ''} - empty string means the row was left blank."""
        if not names:
            return {}
        # Single-flight: if a prompt is already live, merge extra names into it
        # and wait on the same result. Prevents a second thread from opening a
        # ghost dialog that never shows.
        if not hasattr(self, "_pw_prompt_lock"):
            self._pw_prompt_lock = threading.Lock()
            self._pw_prompt_live = None
        with self._pw_prompt_lock:
            live = self._pw_prompt_live
            if live is not None:
                live["extra_names"].update(names)
                return {}
        result = {"map": {}, "ok": False, "extra_names": set()}
        with self._pw_prompt_lock:
            self._pw_prompt_live = result
        done = threading.Event()

        def ask():
            dlg = None
            try:
                dlg = tk.Toplevel(self)
                dlg.title("Login - passwords required")
                dlg.configure(bg=SURFACE)
                try:
                    dlg.transient(self)
                except tk.TclError:
                    pass
                dlg.resizable(False, False)

                header = (f"Enter the password for each account "
                          f"({len(names)} account{'s' if len(names) != 1 else ''}).")
                tk.Label(dlg, text=header, bg=SURFACE, fg=FG, font=FONT,
                         anchor="w", justify="left").grid(row=0, column=0, columnspan=2,
                                                          sticky="ew", padx=16, pady=(16, 10))

                body = tk.Frame(dlg, bg=SURFACE)
                body.grid(row=1, column=0, columnspan=2, sticky="nsew", padx=16)
                body.columnconfigure(1, weight=1)

                entries = {}
                for idx, nm in enumerate(names):
                    tk.Label(body, text=nm, bg=SURFACE, fg=FG, font=FONT_BOLD,
                             anchor="w", width=20).grid(row=idx, column=0, sticky="w",
                                                        padx=(0, 10), pady=4)
                    e = tk.Entry(body, font=FONT, bg=SURFACE2, fg=FG, show="•",
                                 relief="flat", insertbackground=FG, width=28)
                    e.grid(row=idx, column=1, sticky="ew", pady=4)
                    entries[nm] = e

                btns = tk.Frame(dlg, bg=SURFACE)
                btns.grid(row=2, column=0, columnspan=2, sticky="e", padx=16, pady=(14, 16))

                def finish(ok):
                    if ok:
                        result["map"] = {n: entries[n].get() for n in names}
                    result["ok"] = ok
                    try:
                        dlg.grab_release()
                    except tk.TclError:
                        pass
                    try:
                        dlg.destroy()
                    except tk.TclError:
                        pass

                def submit(_e=None):
                    finish(True)

                def cancel(_e=None):
                    finish(False)

                try:
                    GlowButton(btns, text="Cancel", command=cancel, small=True).pack(side="right", padx=(6, 0))
                    GlowButton(btns, text="Log in", kind="primary", command=submit, small=True).pack(side="right")
                except Exception:
                    tk.Button(btns, text="Cancel", command=cancel).pack(side="right", padx=(6, 0))
                    tk.Button(btns, text="Log in", command=submit).pack(side="right")

                dlg.bind("<Return>", submit)
                dlg.bind("<Escape>", cancel)
                dlg.protocol("WM_DELETE_WINDOW", cancel)

                dlg.update_idletasks()
                try:
                    px = self.winfo_rootx() + (self.winfo_width() - dlg.winfo_reqwidth()) // 2
                    py = self.winfo_rooty() + (self.winfo_height() - dlg.winfo_reqheight()) // 2
                    dlg.geometry(f"+{max(px, 0)}+{max(py, 0)}")
                except tk.TclError:
                    pass
                # Non-modal: no grab_set. If the dialog hangs or the user
                # ignores it, the main menu stays fully clickable.
                try:
                    dlg.lift()
                    dlg.focus_force()
                    dlg.attributes("-topmost", True)
                    dlg.after(150, lambda d=dlg: d.attributes("-topmost", False))
                except tk.TclError:
                    pass
                first = entries.get(names[0])
                if first is not None:
                    try:
                        first.focus_set()
                    except tk.TclError:
                        pass
                dlg.wait_window()
            except (tk.TclError, RuntimeError):
                result["ok"] = False
            finally:
                if dlg is not None:
                    try:
                        dlg.grab_release()
                    except tk.TclError:
                        pass
                done.set()

        # Make sure no stale grab from a previous dialog is still held.
        try:
            holder = self.grab_current()
            if holder is not None:
                holder.grab_release()
        except tk.TclError:
            pass

        try:
            if threading.current_thread() is threading.main_thread():
                # No background worker: run the dialog synchronously - a self.after
                # scheduling here would block the mainloop forever.
                ask()
            else:
                try:
                    self.after(0, ask)
                except (tk.TclError, RuntimeError):
                    return {}
                done.wait(timeout=900)
        finally:
            with self._pw_prompt_lock:
                self._pw_prompt_live = None
        if not result["ok"]:
            return {}
        return {n: (v or "").strip() for n, v in result["map"].items()}

    def _cookie_of(self, acc, sess):
        cookie = ""
        try:
            cookie = sess.s.cookies.get(".ROBLOSECURITY") or ""
        except Exception:
            pass
        return cookie or decrypt(acc.get("cookie", ""))

    def _cancelled(self):
        """True when Stop was pressed for the running tool."""
        return self._job_cancel_any.is_set() or self._shutdown_event.is_set()

    def _submit(self, title, kind, fn, *args):
        """Put an account tool in the waiting line; it starts by itself when the ones before it are done."""
        if self._stopping:
            self.log("Still stopping - please try again in a moment.")
            return False
        ahead = self.jobs.submit(title, kind, fn, *args)
        if ahead > 0:
            self.log(f"{title} is waiting in line (position {ahead}) - it starts when the current action is done.")
        return True

    def _workers(self, n):
        """Parallel account workers: enough for speed, capped so many accounts do not flood RAM / Roblox."""
        return max(1, min(int(n), 4 if self.extreme_save_mode.get() else 8))

    def _wait_for(self, check, seconds, interval=1.0):
        end = time.time() + seconds
        while True:
            try:
                if check():
                    return True
            except Exception:
                pass
            if time.time() >= end or self._cancelled():
                return False
            self._shutdown_event.wait(interval)

    def _bio_matches(self, sess, text):
        r = sess.req("GET", "https://users.roblox.com/v1/description", retries=2)
        if r is None or r.status_code != 200:
            return False
        return (r.json().get("description") or "").strip() == text.strip()

    def _display_matches(self, sess, uid, new):
        r = sess.req("GET", f"https://users.roblox.com/v1/users/{uid}", retries=2)
        return r is not None and r.status_code == 200 and r.json().get("displayName") == new

    def _is_following(self, sess, target_id):
        r = sess.req("POST", "https://friends.roblox.com/v1/user/following-exists",
                     json={"targetUserIds": [int(target_id)]}, retries=2)
        if r is None or r.status_code != 200:
            return False
        try:
            return any(f.get("isFollowing") for f in r.json().get("followings", []))
        except Exception:
            return False

    def _stop_on_limit(self, name, label, reason):
        with self._limit_lock:
            self._limit_names.add(name)
        self.log(f"{name}: {label} stopped - limit reached ({reason}). Try again later.")
        return False

    def _browser_attempts(self, label, name, tries, api_step, ui_step, verify, user_wait=150):
        """Click through the page, then try the in-page API call; wait only a few seconds for each.
        The long wait for the user happens only when Roblox really answered with a verification request."""
        warned = False
        for attempt in range(1, tries + 1):
            if self._cancelled():
                return False
            challenged = False
            code = None
            try:
                code = ui_step()
            except Exception as exc:
                self.log(f"{name}: browser step failed ({str(exc)[:80]}).")
            if code == "ratelimit":
                self.log(f"{name}: Roblox asked to slow down - waiting, then trying again.")
                self._rate_wait("browser", 20)
                continue
            if code == "limit":
                if self._wait_for(verify, 2, 0.4):
                    return True
                return self._stop_on_limit(name, label, "Roblox said wait before changing this again")
            if self._wait_for(verify, 5, 0.4):
                return True
            try:
                result = api_step()
                if isinstance(result, tuple) and len(result) >= 3:
                    challenged = bool(result[2])
                    body_text = json.dumps(result[1]) if result[1] else ""
                    reason = self._limit_reason(result[0], body_text)
                    if reason and not challenged:
                        if self._wait_for(verify, 2, 0.4):
                            return True
                        return self._stop_on_limit(name, label, reason)
                    if not challenged and self._is_rate_limit(result[0], body_text):
                        self.log(f"{name}: Roblox asked to slow down - waiting, then trying again.")
                        self._rate_wait("browser", 20)
                        continue
            except Exception:
                pass
            if self._wait_for(verify, 3, 0.4):
                return True
            if challenged and not warned:
                warned = True
                self.log(f"{name}: Roblox asks for a verification - please complete it in the {label} "
                         f"Edge window (waiting up to {user_wait // 60} min).")
                if self._wait_for(verify, user_wait, 2.0):
                    return True
            elif attempt < tries:
                self.log(f"{name}: {label} not applied yet, trying again ({attempt}/{tries}).")
        return False

    # ---------- Accounts ----------
    def add_account(self, login):
        try:
            name, pw = self.e_user.get().strip(), self.e_pass.get()
            if not name or not pw:
                messagebox.showwarning("Missing info", "Please enter a username and a password.")
                return
            if any(a["name"].lower() == name.lower() for a in self.accounts):
                messagebox.showinfo("Already added", f"'{name}' is already in the list.")
                return
            acc = {"name": name, "password": encrypt(pw), "cookie": ""}
            self.accounts.append(acc)
            if not self._save():
                self.accounts.pop()
                return
            self.checked.add(name)
            self.e_user.delete(0, "end")
            self.e_pass.delete(0, "end")
            self._refresh_list()
            self.log(f"{name}: saved.")
            if login:
                def work():
                    try:
                        self._sessions_for([acc], prompt_missing=True)
                    except Exception as e:
                        self.log(f"{name}: error - {e}")
                threading.Thread(target=work, daemon=True).start()
        except Exception as e:
            self.log(f"Could not save: {e}")
            messagebox.showerror("Error", str(e))

    def relogin_selected(self):
        sel = self._selected()
        if not sel:
            messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        backup = {a["name"]: a.get("cookie", "") for a in sel}
        for a in sel:
            a["cookie"] = ""
            with self._sessions_lock:
                self.session_cache.pop(a["name"].lower(), None)
        self._refresh_list()

        def work():
            try:
                self._sessions_for(sel, prompt_missing=True)
            except Exception as e:
                self.log(f"Error: {e}")
            finally:
                for a in sel:  # a login that failed or was cancelled keeps the previous cookie
                    if not a.get("cookie") and backup.get(a["name"]):
                        a["cookie"] = backup[a["name"]]
                self._save()
                try:
                    self.after(0, self._refresh_list)
                except (tk.TclError, RuntimeError):
                    pass
        threading.Thread(target=work, daemon=True).start()

    def remove_selected(self):
        sel = self._selected()
        if not sel:
            messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        if not messagebox.askyesno("Remove accounts", f"Remove {len(sel)} account(s) from the list?"):
            return
        for a in sel:
            info = self.tracked.pop(a["name"], None)
            self.relaunch_on.discard(a["name"])
            if info:
                info["stopped"] = True
                kill_pid(info["pid"])
            with self._sessions_lock:
                self.session_cache.pop(a["name"].lower(), None)
            self.accounts.remove(a)
            self.checked.discard(a["name"])
        self._save()
        self._refresh_list()
        self._notify_state_changed()

    # ---------- Friends ----------
    def _save_friends_cache(self, cache, rows, owners):
        try:
            data = {"cache": [list(c) for c in cache], "rows": [list(r) for r in rows],
                    "owners": {str(k): v for k, v in owners.items()}, "time": int(time.time())}
            tmp = FRIENDS_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f)
            os.replace(tmp, FRIENDS_FILE)
        except (OSError, ValueError, TypeError):
            pass

    def _restore_friends(self):
        """Show the friends saved last time right away; the reload then brings them up to date."""
        try:
            with open(FRIENDS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            cache = [(int(c[0]), str(c[1]), str(c[2])) for c in data["cache"]]
            rows = [(int(r[0]), str(r[1]), str(r[2]), str(r[3])) for r in data["rows"]]
            owners = {int(k): list(v) for k, v in data["owners"].items()}
        except (OSError, ValueError, TypeError, KeyError, IndexError):
            return
        self._show_friends(cache, rows, owners, {})

    def _show_friends(self, cache, rows, owners, thumbs):
        if self.closing:
            return
        self.friend_cache = cache
        self.friend_owners = owners
        self.friend_list.delete(*self.friend_list.get_children())
        self.friend_imgs = {}
        for i, (fid, text, state, accs) in enumerate(rows):
            img = None
            if fid in thumbs:
                try:
                    img = tk.PhotoImage(data=base64.b64encode(thumbs[fid]))
                except Exception:
                    img = None
            kw = {"image": img} if img else {}
            if img:
                self.friend_imgs[i] = img
            tag = {"In game": "ingame", "Online": "online", "In Studio": "online"}.get(state, "offline")
            self.friend_list.insert("", "end", iid=str(i), text="  " + text,
                                    values=(state, accs), tags=(tag,), **kw)

    def load_friends(self, auto=False):
        """Reload the friend list. auto=True: quietly, with every saved account, and never opens a login."""
        sel = self._selected()
        if not sel and auto:
            sel = [a for a in self.accounts if a.get("cookie")]
        if not sel:
            if not auto:
                messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        if not auto:
            self.log(f"Reloading friends of {len(sel)} account(s) ...")

        def work():
            try:
                sessions = self._sessions_for(sel, allow_login=not auto)
                pairs = [(a, s_) for a, s_ in zip(sel, sessions) if s_ and self._ensure_id(a, s_)]
                if not pairs:
                    if not auto:
                        self.log("No valid account session; cannot load friends.")
                    return

                def fetch(pair):
                    acc, sess = pair
                    fl = sess.friends(acc["id"])
                    pres = {}
                    if fl:
                        try:
                            pres = {p["userId"]: p for p in sess.presence([f["id"] for f in fl])}
                        except Exception:
                            pres = {}
                    return acc, fl, pres, sess.last_status

                with ThreadPoolExecutor(max_workers=min(4, len(pairs))) as ex:
                    results = list(ex.map(fetch, pairs))

                merged = {}
                for acc, fl, pres, status in results:
                    if fl is None:
                        self.log(f"{acc['name']}: friends could not be loaded (Roblox status {status}).")
                        continue
                    for f in fl:
                        entry = merged.setdefault(f["id"], {
                            "name": f["name"], "display": f.get("displayName", f["name"]),
                            "owners": set(), "type": 0})
                        entry["owners"].add(acc["name"])
                        entry["type"] = max(entry["type"], pres.get(f["id"], {}).get("userPresenceType", 0))
                if not merged:
                    return
                order = sorted(merged.items(), key=lambda kv: (-kv[1]["type"], kv[1]["display"].lower()))
                thumbs = self._download_headshots([fid for fid, _ in order])
                states = {0: "Offline", 1: "Online", 2: "In game", 3: "In Studio"}
                cache, rows, owners = [], [], {}
                for fid, e in order:
                    cache.append((fid, e["name"], e["display"]))
                    owners[fid] = sorted(e["owners"])
                    rows.append((fid, f"{e['display']} (@{e['name']})", states.get(e["type"], "Offline"),
                                 f"{len(e['owners'])}/{len(pairs)}"))
                self._save_friends_cache(cache, rows, owners)
                self.after(0, lambda: self._show_friends(cache, rows, owners, thumbs))
                self.log(f"{len(rows)} unique friends loaded from {len(pairs)} account(s).")
            except Exception as e:
                if not auto:
                    self.log(f"Could not load friends: {e}")
        self._submit("Reload friends", "FRIENDS", work, )

    def _download_headshots(self, ids):
        urls, out = {}, {}
        chunks = [ids[i:i + 100] for i in range(0, len(ids), 100)]

        def fetch_chunk(chunk):
            try:
                r = requests.get("https://thumbnails.roblox.com/v1/users/avatar-headshot",
                                 params={"userIds": ",".join(map(str, chunk)), "size": "48x48", "format": "Png"},
                                 timeout=15)
                return [(d["targetId"], d["imageUrl"]) for d in r.json().get("data", []) if d.get("imageUrl")]
            except Exception:
                return []

        def get(item):
            try:
                resp = requests.get(item[1], timeout=15)
                return item[0], resp.content if resp.status_code == 200 else None
            except Exception:
                return item[0], None

        with ThreadPoolExecutor(max_workers=6) as ex:
            for pairs in ex.map(fetch_chunk, chunks):
                urls.update(pairs)
            for uid, data in ex.map(get, urls.items()):
                if data:
                    out[uid] = data
        return out

    # ---------- Specific users and follows ----------
    def _resolve_specific_user_worker(self, text, callback):
        selected = self._selected()
        try:
            session = self._sessions_for([selected[0]])[0] if selected else None
            if session is None:
                session = RobloxSession("")  # user lookup works without login
            user = session.resolve_user(text)
            if not user:
                self.log(f"Roblox user '{text}' was not found.")
                return
            callback(user)
        except Exception as exc:
            self.log(f"Could not resolve Roblox user: {exc}")

    def add_specific_user(self):
        text = self.e_target.get().strip()
        if not text:
            messagebox.showinfo("Add a specific user", "Enter a Roblox username or display name first.")
            return
        self.log(f"Looking up '{text}' ...")

        def store(user):
            uid, username, display = user
            self.target_user = (int(uid), str(username), str(display))
            self.specific_users = [u for u in self.specific_users if int(u.get("id", 0)) != int(uid)]
            self.specific_users.append({"id": int(uid), "name": str(username), "displayName": str(display)})
            self._persist_settings()
            self._render_saved_users()
            self.e_target.delete(0, "end")
            self.e_target.insert(0, username)
            self.mode.set("user")
            self.log(f"Added {display} (@{username}). Launch will join this user.")

        threading.Thread(
            target=lambda: self._resolve_specific_user_worker(text, lambda u: self.after(0, lambda: store(u))),
            name="CrimsonAddSpecificUser", daemon=True
        ).start()

    def follow_specific_user(self):
        text = self.e_target.get().strip()
        selected = self._selected()
        if not selected or not text:
            messagebox.showinfo("Follow user", "Select account(s) and enter a user to follow.")
            return

        def work():
            fleet = BrowserFleet(self)
            try:
                started = time.time()
                sessions = self._sessions_for(selected)
                pairs = [(a, s_) for a, s_ in zip(selected, sessions) if s_ and self._ensure_id(a, s_)]
                if not pairs:
                    self.log("No valid selected account session is available.")
                    return
                target = pairs[0][1].resolve_user(text)
                if not target:
                    self.log(f"Roblox user '{text}' was not found.")
                    return
                tid, tname, tdisp = target
                pairs = [(a, s_) for a, s_ in pairs if int(a["id"]) != int(tid)]
                if not pairs:
                    self.log("Cannot follow the same account.")
                    return

                tick = self.jobs.ticker(len(pairs))
                fleet.prestart(pairs)

                def fast(pair):
                    acc, sess = pair
                    name = acc["name"]
                    if self._cancelled():
                        tick()
                        return None
                    if self._is_following(sess, tid):
                        self.log(f"{name}: already following {tdisp} (@{tname}).")
                        tick()
                        return None
                    response = sess.req("POST", f"https://friends.roblox.com/v1/users/{tid}/follow", retries=2)
                    if (response is not None and response.status_code in (200, 201, 204)) \
                            or self._is_following(sess, tid):
                        self.log(f"{name}: now following {tdisp} (@{tname}).")
                        tick()
                        return None
                    return pair

                with ThreadPoolExecutor(max_workers=self._workers(len(pairs))) as ex:
                    pending = [x for x in ex.map(fast, pairs) if x]
                for pair in pairs:
                    if pair not in pending:
                        fleet.release(pair[0])
                if pending:
                    self.log(f"Following in {len(pending)} browser window(s) (Roblox asked for a check) ...")
                    fleet.open(pending)

                    def slow(pair):
                        acc, sess = pair
                        name = acc["name"]
                        browser = fleet.get(acc)
                        if browser and self._browser_attempts(
                                "follow", name, 3,
                                lambda: browser.api(f"https://friends.roblox.com/v1/users/{tid}/follow", "POST", None),
                                lambda: browser.ui_follow(tid),
                                lambda: self._is_following(sess, tid)):
                            self.log(f"{name}: now following {tdisp} (@{tname}).")
                        elif not self._limit_hit(name):
                            self.log(f"{name}: could not follow @{tname}.")
                        fleet.release(acc)
                        tick()

                    with ThreadPoolExecutor(max_workers=self._workers(len(pending))) as ex:
                        list(ex.map(slow, pending))
                self.log(f"Done: follow finished in {time.time() - started:.1f} s.")
            except Exception as exc:
                self.log(f"Follow error: {exc}")
            finally:
                fleet.close()

        self._submit("Follow user", "FOLLOWING", work)

    # ---------- Launch ----------
    def _current_spec(self):
        mode = self.mode.get()
        text = self.e_target.get().strip()
        fsel = self.friend_list.selection()
        friend = self.friend_cache[int(fsel[0])] if fsel and self.friend_cache else None
        if mode == "game":
            place_id = parse_game_id(self.e_place.get())
            if not place_id:
                messagebox.showinfo("Game ID", "Enter a game ID or paste a game link first.")
                return None
            job_id, valid = parse_server_id(self.e_job.get())
            if not valid:
                messagebox.showinfo("Server ID", "That does not look like a server ID (it looks like 8-4-4-4-12 letters and digits).")
                return None
            return {"mode": "game", "friend": None, "text": str(place_id), "target_user": None,
                    "place_id": place_id, "job_id": job_id or None, "game_name": self._game_name(place_id)}
        if mode == "friend" and not friend:
            messagebox.showinfo("Pick a friend", "Select a friend in the list. If it is empty, press 'Reload friends'.")
            return None
        target_user = None
        if mode == "user":
            if not text:
                messagebox.showinfo("Add a specific user", "Enter a username first.")
                return None
            tu = self.target_user
            if tu and text.lstrip("@").lower() in {tu[1].lower(), tu[2].lower()}:
                target_user = tu
        return {"mode": mode, "friend": friend, "text": text, "target_user": target_user}

    @staticmethod
    def _presence_join(sess, target_id):
        try:
            pres = sess.presence([target_id])
        except Exception:
            return None
        p = pres[0] if pres else {}
        if p.get("userPresenceType") == 2 and p.get("placeId"):
            return p["placeId"], p.get("gameId")
        return None

    def _resolve_join(self, sess, spec):
        """-> (place_id, game_id). Any selected account that can see the target's game is enough:
        the other accounts then join that same server."""
        mode = spec["mode"]
        if mode == "app":
            return None, None
        if mode == "game":
            return spec["place_id"], spec.get("job_id")
        target = spec["friend"] if mode == "friend" else (spec.get("target_user") or sess.resolve_user(spec["text"]))
        if not target:
            self.log(f"User '{spec['text']}' not found - starting Roblox only.")
            return None, None
        spec["target_user"] = target
        tid = target[0]
        found = self._presence_join(sess, tid)
        if not found:
            cached = self._join_cache.get(tid)
            if cached and time.time() - cached[2] < 300:
                found = (cached[0], cached[1])
        if not found:
            with self._sessions_lock:
                others = [x for x in self.session_cache.values() if x is not sess]
            for other in others:
                found = self._presence_join(other, tid)
                if found:
                    break
        if found:
            self._join_cache[tid] = (found[0], found[1], time.time())
            return found
        self.log(f"{target[2]} is not in a joinable game right now - starting Roblox only.")
        return None, None

    @staticmethod
    def _format_remaining(seconds):
        seconds = max(0, int(seconds))
        return f"{seconds // 60:02d}:{seconds % 60:02d}"

    def _launch_progress(self, message):
        if self.closing:
            return
        try:
            self.after(0, lambda m=message: self.header_state.config(text=m[:48]))
        except tk.TclError:
            pass

    def _wait_stable(self, pid, cancel_event):
        """Wait until the new client has shown that it works. -> (ok, reason)
        Fails when the process closes OR when it opens an error window (authentication error, disconnect ...)."""
        end = time.monotonic() + STABLE_SECONDS
        t_begin = time.monotonic()
        while time.monotonic() < end:
            self._stage_frac(0.65 + 0.3 * min(1.0, (time.monotonic() - t_begin) / max(1.0, STABLE_SECONDS)))
            if cancel_event.wait(0.5) or self._shutdown_event.is_set():
                return True, ""
            current, _ = process_snapshot(verbose=False)
            if current is not None and pid not in current:
                return False, "Roblox closed right after starting"
            state, text, strong = classify_client(True, False, 0, client_windows([pid]).get(pid, []))
            if state == "error" and strong:
                return False, text
        return True, ""

    def _fresh_login(self, acc, cancel_event):
        """Throw the saved cookie away and sign in again (used after repeated authentication errors)."""
        old_cookie = acc.get("cookie", "")
        acc["cookie"] = ""
        with self._sessions_lock:
            self.session_cache.pop(acc["name"].lower(), None)
        refreshed = self._sessions_for([acc], cancel_event=cancel_event, force_fresh=True)
        if not acc.get("cookie") and old_cookie:
            acc["cookie"] = old_cookie
        return refreshed[0] if refreshed else None

    def _launch_one(self, acc, sess, spec, cancel_event=None):
        """Start one client, retrying up to 15 times within a five-minute window."""
        name = acc["name"]
        cancel_event = cancel_event or self._shutdown_event
        with self.launch_lock:
            if cancel_event.is_set() or self._shutdown_event.is_set():
                return False
            self._prog_stage(name, "preparing the graphics profile", 0.05)
            self._apply_profile_for(acc)
            self._prog_stage(name, "finding the game", 0.12)
            place_id, game_id = self._resolve_join(sess, spec)
            if place_id:
                self.log(f"{name}: joining " + (spec.get("game_name") or f"place {place_id}")
                         + (" on the chosen server." if game_id and spec.get("mode") == "game" else "."))

            deadline = time.monotonic() + RETRY_WINDOW_SECONDS
            reauth_attempted = False
            quick_crashes = 0
            uri_variant = 0
            first_before = None
            no_start = 0
            t_launch = time.monotonic()
            for attempt in range(1, MAX_RETRIES + 1):
                if cancel_event.is_set() or self._shutdown_event.is_set():
                    self.log(f"{name}: launch cancelled.")
                    return False
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break

                snap, _ = process_snapshot(verbose=False)
                if snap is not None and first_before is None:
                    first_before = set(snap)
                before = first_before if first_before is not None else snap
                if snap is None:
                    self.log(f"{name}: Windows process check unavailable (attempt {attempt}/{MAX_RETRIES}).")
                    cancel_event.wait(min(2.0, max(0.0, deadline - time.monotonic())))
                    continue

                self._prog_stage(name, "requesting the launch ticket", 0.2)
                try:
                    ticket = sess.auth_ticket()
                except requests.RequestException:
                    ticket = None
                    self.log(f"{name}: connection problem while requesting the launch ticket. {self._net_hint(True)}".strip())
                if not ticket:
                    if getattr(sess, "last_auth_state", "unknown") == "invalid" and not reauth_attempted:
                        reauth_attempted = True
                        self.log(f"{name}: saved Roblox session expired; refreshing sign-in ...")
                        refreshed = self._sessions_for([acc], cancel_event=cancel_event)
                        if refreshed and refreshed[0]:
                            sess = refreshed[0]
                            continue
                    remaining = deadline - time.monotonic()
                    self.log(f"{name}: Roblox gave no launch ticket (try {attempt}/{MAX_RETRIES}). {self._net_hint()}".strip())
                    cancel_event.wait(min(1.5, max(0.0, remaining)))
                    continue

                try:
                    os.startfile(build_uri(ticket, place_id, game_id, uri_variant))
                except OSError as exc:
                    self.log(f"{name}: Windows could not open Roblox: {exc}")
                    cancel_event.wait(1.0)
                    continue

                remaining = deadline - time.monotonic()
                self._prog_stage(name, "starting Roblox" if attempt == 1 else f"starting Roblox again (try {attempt})", 0.3)
                self.log(f"{name}: starting Roblox ..." if attempt == 1
                         else f"{name}: starting Roblox again (try {attempt}/{MAX_RETRIES}) ...")
                end = min(deadline, time.monotonic() + min(WAIT_PER_TRY, max(1.0, remaining)))
                probe_interval = self._launch_probe_interval()
                while time.monotonic() < end:
                    if cancel_event.is_set() or self._shutdown_event.is_set():
                        self.log(f"{name}: launch cancelled.")
                        return False
                    remaining = deadline - time.monotonic()
                    self._launch_progress(f"{name} · {attempt}/{MAX_RETRIES} · {self._format_remaining(remaining)}")
                    wait_for = min(probe_interval, max(0.05, end - time.monotonic()))
                    if cancel_event.wait(wait_for) or self._shutdown_event.is_set():
                        self.log(f"{name}: launch cancelled.")
                        return False
                    current, _ = process_snapshot(verbose=False)
                    if current is None:
                        continue
                    new_pids = current - before
                    if new_pids:
                        pid = min(new_pids)
                        self.log(f"{name}: Roblox opened, checking that it stays open ...")
                        self._prog_stage(name, "Roblox opened - checking that it stays open", 0.65)
                        stable, why = self._wait_stable(pid, cancel_event)
                        if not stable:
                            kill_pid(pid)  # close the error window / dead client before the next try
                            quick_crashes += 1
                            if "authentication" in why.lower() or "(403)" in why:
                                quick_crashes = max(quick_crashes, 2)  # a rejected login needs a fresh login right away
                            self.log(f"{name}: client problem - {why} (attempt {attempt}/{MAX_RETRIES}).")
                            sess.csrf = None
                            uri_variant = (uri_variant + 1) % 3
                            self.log(f"{name}: trying a different start method ({uri_variant + 1}/3) ...")
                            if quick_crashes >= 2:
                                self.log(f"{name}: signing in again to get a fresh login ...")
                                fresh = self._fresh_login(acc, cancel_event)
                                if fresh:
                                    sess = fresh
                                    quick_crashes = 0
                            elif sess.me(retries=1) is None and getattr(sess, "last_auth_state", "") == "invalid":
                                fresh = self._fresh_login(acc, cancel_event)
                                if fresh:
                                    sess = fresh
                            cancel_event.wait(3.0)
                            break
                        previous = self.tracked.get(name, {})
                        self.tracked[name] = {
                            "pid": pid, "spec": spec, "sess": sess,
                            "since": time.time(), "joined": bool(place_id),
                            "restarts": previous.get("restarts", []), "hung": 0,
                            "notin": 0, "lastpres": 0, "restarting": False,
                            "state": "working", "state_text": "Running", "errseen": 0, "presence": None,
                        }
                        self.log(f"{name}: running - ready in {int(time.monotonic() - t_launch)} s.")
                        self._prog_stage(name, "running", 1.0)
                        self._after_client_started(pid, name)
                        self._notify_state_changed()
                        return True

                no_start += 1
                if no_start == 3 and self._auto_fix_on:
                    self.log(f"{name}: Auto-fix - cleaning Roblox leftovers and checking the settings ...")
                    clear_roblox_cache()
                    repair_roblox_settings()
                    if not MULTI["ok"]:
                        hold_singleton_mutex()
                if no_start in (2, 4) and not (cancel_event.is_set() or self._shutdown_event.is_set()):
                    self.log(f"{name}: Roblox is not starting - restarting Microsoft Edge and refreshing the sign-in. "
                             f"{self._net_hint(True)}".strip())
                    kill_edge_tree(None)
                    sess.csrf = None
                    if no_start >= 4:
                        fresh = self._fresh_login(acc, cancel_event)
                        if fresh:
                            sess = fresh

            self.log(f"{name}: Roblox did not start. "
                     + (self._net_hint(True) or "Close leftover Roblox windows, then try again."))
            return False

    def _ensure_multi_instance(self):
        """Several clients only work when this program owns Roblox's single-instance mutex. When a Roblox client
        that was not started here is already open, close it and take the mutex."""
        if MULTI["ok"] and _mutex_handle:
            return
        live = [i for i in self.tracked.values() if not i.get("stopped")]
        foreign = native_roblox_pids()
        if foreign and not live:
            self.log("Closing Roblox clients that were not started here so that several accounts can run ...")
            ok = repair_multi_instance()
        else:
            hold_singleton_mutex()
            ok = bool(MULTI["ok"])
        self.log("Multi-instance ready." if ok else f"Multi-instance is blocked: {MULTI['note']}.")
        try:
            self.after(0, self._update_multi_badge)
        except (tk.TclError, RuntimeError):
            pass

    def _boosted(self, name):
        """Rocket on: this account runs with the performance profile."""
        return name not in self.perf_off

    def _prepare_lean(self):
        """Kept for the launch paths; the profile is written per account in _apply_profile_for."""
        return

    def _apply_profile_for(self, acc):
        name = acc["name"]
        perf = bool(self.performance_mode.get()) and self._boosted(name)
        try:
            cap = int(self.fps_cap.get())
        except ValueError:
            cap = 0
        cap = cap if (perf and self.lean_clients.get() and cap > 0) else None
        changed, message = apply_profile(perf, cap, bool(self.mute_clients.get()),
                                          {**pack_flags([k for k, v in self.flag_packs.items() if v.get()]), **load_custom_flags()},
                                          high=not perf)
        if message:
            self.log(f"{name}: {message}")

    def _after_client_started(self, pid, name=None):
        """Boosted account: lower priority at once, trim memory once the client has settled."""
        return  # lowering priority or trimming a running Roblox makes it stutter and answer slowly

        def work():
            started = time.time()
            while not self._shutdown_event.wait(3.0):
                info = self.tracked.get(name) if name else None
                if info is not None and info.get("pid") != pid:
                    return
                age = time.time() - started
                if age > 600 or (age >= 90 and (info is None or info.get("state") == "working")):
                    break
            else:
                return
            slim_down_client(pid, trim=False)
            if self._shutdown_event.wait(15):
                return
            slim_down_client(pid, trim=True)
        threading.Thread(target=work, name="Multi-LauncherSlim", daemon=True).start()

    def _begin_launch_ui(self, state_text="LAUNCHING"):
        self.busy = True
        # Starting a new launch is an explicit request to resume launcher work
        # after an earlier emergency stop.
        self._action_cancel_event.clear()
        self._launch_cancel_event.clear()
        self.btn_launch.config(text="STOP LAUNCH", command=self.cancel_launch, state="normal")
        self.header_state.config(text=state_text)

    def _finish_launch_ui(self):
        self.busy = False
        self._prog_end()
        if (self.auto_tile.get() or self.tiny_windows.get()) and not self.closing:
            try:
                self.after(0, lambda: self.after(4000, lambda: self.tile_windows(quiet=True)))
            except (tk.TclError, RuntimeError):
                pass
        self._notify_state_changed()
        if not self.closing:
            try:
                self.after(0, lambda: self.btn_launch.config(
                    text="LAUNCH SELECTED", command=self.launch, state="normal"
                ))
                self.after(0, lambda: self.header_state.config(text="READY"))
            except tk.TclError:
                pass

    def cancel_launch(self):
        if not self.busy:
            return
        self._launch_cancel_event.set()
        self.log("Launch queue stopped. Clients already started will remain open.")
        try:
            self.btn_launch.config(text="STOPPING ...", state="disabled")
            self.header_state.config(text="STOPPING")
        except tk.TclError:
            pass

    def launch(self):
        if self.busy:
            return
        selected = self._selected()
        if not selected:
            messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        spec = self._current_spec()
        if spec is None:
            return
        self._begin_launch_ui()
        threading.Thread(
            target=self._launch_worker, args=(selected, spec),
            name="CrimsonLaunchWorker", daemon=True
        ).start()

    def _launch_worker(self, selected, spec):
        try:
            self._apply_speed(len(selected))
            self._prog_start("Launching", len(selected))
            threading.Thread(target=self._precheck_clock, name="ClockCheck", daemon=True).start()
            threading.Thread(target=self._precheck_net, name="NetPrecheck", daemon=True).start()
            self._ensure_multi_instance()
            if self._auto_fix_on:
                self._autofix_quick()
            self._prepare_lean()
            self._prog_stage("", f"checking saved sign-ins for {len(selected)} account(s)")
            self.log(f"Checking saved sign-ins for {len(selected)} account(s) ...")
            if spec.get("mode") == "game":
                self._remember_game(spec["place_id"], spec.get("game_name", ""))
            # Sort: accounts that already have a cookie come first. The ones
            # that still need Edge are pushed to the end, so every Ready
            # account launches without waiting on a slow login.
            selected = sorted(selected, key=lambda a: 0 if a.get("cookie") else 1)
            sessions = self._sessions_for(selected, cancel_event=self._launch_cancel_event)
            self._warm_sessions(sessions)
            started = 0
            deferred = []  # accounts that crashed/failed on the first pass - retried at the end
            for acc, session in zip(selected, sessions):
                if self._launch_cancel_event.is_set() or self._shutdown_event.is_set():
                    break
                if not session:
                    self.log(f"{acc['name']}: no valid session available; skipped.")
                    self._prog_account_done(False)
                    continue
                launched_ok = self._launch_one(acc, session, spec, cancel_event=self._launch_cancel_event)
                if launched_ok:
                    self._prog_account_done(True)
                    started += 1
                    if self._launch_cancel_event.wait(LAUNCH_PAUSE):
                        break
                else:
                    # Crashed / failed: keep going with the rest, come back to it
                    # once every other account has had its first shot.
                    deferred.append((acc, session))
                    self.log(f"{acc['name']}: crashed on first try - queued for a retry after the rest.")
            # Retry pass: anything that failed above is tried again now.
            for acc, session in deferred:
                if self._launch_cancel_event.is_set() or self._shutdown_event.is_set():
                    self._prog_account_done(False)
                    continue
                self.log(f"{acc['name']}: retry pass - starting again.")
                launched_ok = self._launch_one(acc, session, spec, cancel_event=self._launch_cancel_event)
                self._prog_account_done(bool(launched_ok))
                if launched_ok:
                    started += 1
                    if self._launch_cancel_event.wait(LAUNCH_PAUSE):
                        break
            if self._launch_cancel_event.is_set():
                self.log(f"Launch queue cancelled. {started}/{len(selected)} client(s) were started.")
            else:
                self.log(f"Done: {started}/{len(selected)} accounts running.")
                if started < len(selected):
                    hint = self._net_hint(True)
                    if hint:
                        self.log(f"Some accounts did not start. {hint}")
                self.after(0, lambda s_=started, n_=len(selected): self.toast(f"{s_}/{n_} accounts running", bad=s_ < n_))
        except Exception as exc:
            self.log(f"Launch error: {exc}")
        finally:
            try:
                self._sync_cookies()
            except Exception:
                pass
            self._finish_launch_ui()

    # ---------- Stop / restart ----------
    def stop_selected(self):
        for a in self._selected():
            info = self.tracked.pop(a["name"], None)
            if info:
                info["stopped"] = True  # a stopped account is never relaunched
                kill_pid(info["pid"])
                self.log(f"{a['name']}: stopped.")
        self._notify_state_changed()

    def stop_all(self):
        """Compatibility alias for older callers; use the complete action stop."""
        self.stop_all_actions()

    def stop_all_actions(self):
        """Stop everything for a moment: cancel the running tool, empty the waiting line, close the clients and the
        launcher's own Edge windows - and then be ready for new actions again (the stop never stays on)."""
        if self._stopping:
            return
        self._stopping = True
        self._action_cancel_event.set()
        self._launch_cancel_event.set()
        self._monitor_event.set()
        dropped = self.jobs.stop()
        clients = list(self.tracked.items())
        self.tracked.clear()  # keeps the watchdog from restarting what we are closing
        waiting = f" and {dropped} waiting action(s)" if dropped else ""
        self.log(f"Stopping: cancelling the running action{waiting}, closing {len(clients)} client(s) ...")
        self._notify_state_changed()
        if not self.closing:
            try:
                self.btn_launch.config(text="STOPPING ...", state="disabled")
                self.header_state.config(text="STOPPING")
            except tk.TclError:
                pass
        self.after(0, self._render_status)

        def finish():
            try:
                for _name, info in clients:
                    kill_pid(info.get("pid", 0))
                kill_edge_tree(None)
                end = time.time() + 10
                while (self.busy or self.jobs.busy()) and time.time() < end and not self._shutdown_event.is_set():
                    time.sleep(0.2)
                if self.jobs.busy():
                    self.log("The previous action is still winding down; new actions start right after it.")
            finally:
                self._action_cancel_event.clear()   # the stop is over - everything works again
                if not self.busy:
                    self._launch_cancel_event.clear()
                self._stopping = False
                self.log(f"Done: stopped {len(clients)} client(s). Ready for new actions.")
                if not self.closing:
                    try:
                        def reset():
                            if not self.busy:
                                self.btn_launch.config(text="LAUNCH SELECTED", command=self.launch, state="normal")
                                self.header_state.config(text="READY")
                            self._render_status()
                        self.after(0, reset)
                    except tk.TclError:
                        pass

        threading.Thread(target=finish, name="CrimsonStop", daemon=True).start()

    def restart_all(self):
        if self.busy:
            return
        spec = self._current_spec()
        if spec is None:
            return
        names = [a["name"] for a in self._selected()]
        accounts = [a for a in self.accounts if a["name"] in names]
        if not accounts:
            messagebox.showinfo("Nothing to restart", "Select the accounts you want to restart first.")
            return
        self._begin_launch_ui("RESTARTING")

        def work():
            try:
                for account in accounts:
                    if self._launch_cancel_event.is_set():
                        break
                    info = self.tracked.pop(account["name"], None)
                    if info:
                        info["stopped"] = True
                        kill_pid(info["pid"])
                self._apply_speed(len(accounts))
                self._prog_start("Restarting", len(accounts))
                self.log(f"Restarting {len(accounts)} client(s) ...")
                if self._launch_cancel_event.wait(0.3):
                    return
                self._prepare_lean()
                sessions = self._sessions_for(accounts, cancel_event=self._launch_cancel_event)
                ok = 0
                for account, session in zip(accounts, sessions):
                    if self._launch_cancel_event.is_set() or self._shutdown_event.is_set():
                        break
                    restarted = bool(session) and self._launch_one(account, session, spec, cancel_event=self._launch_cancel_event)
                    self._prog_account_done(bool(restarted))
                    if restarted:
                        ok += 1
                        if self._launch_cancel_event.wait(LAUNCH_PAUSE):
                            break
                if self._launch_cancel_event.is_set():
                    self.log(f"Restart queue cancelled. {ok}/{len(accounts)} client(s) restarted.")
                else:
                    self.log(f"Restart finished: {ok}/{len(accounts)} running.")
            except Exception as exc:
                self.log(f"Restart error: {exc}")
            finally:
                self._finish_launch_ui()

        threading.Thread(target=work, name="CrimsonRestartWorker", daemon=True).start()

    # ---------- Watchdog: automatic restart ----------
    def _watchdog(self):
        """Adaptive monitor: sleeps while idle and shares one process snapshot per cycle."""
        while not self._shutdown_event.is_set():
            active = bool(self.tracked)
            timeout = self._monitor_interval() if active else 30.0
            self._wait_or_death(timeout)
            self._monitor_event.clear()
            if self._shutdown_event.is_set():
                break
            if self._action_cancel_event.is_set():
                # Stop All Actions clears tracked clients, but this guard also
                # covers a recovery worker that was already waking up.
                continue
            if not self.tracked:
                continue

            try:
                pids, hung = process_snapshot()
                if pids is None or hung is None:
                    self.log("Windows process monitoring is temporarily unavailable; recovery checks skipped.")
                    continue
                now = time.time()
                windows = client_windows([i["pid"] for i in self.tracked.values() if not i.get("stopped")])
                for name, info in list(self.tracked.items()):
                    if info.get("stopped") or info.get("restarting") or now < info.get("next_try", 0):
                        continue
                    info["hung"] = info.get("hung", 0) + 1 if info["pid"] in hung else 0
                    verdict = classify_client(info["pid"] in pids, info["pid"] in hung, now - info["since"],
                                              windows.get(info["pid"], []), info.get("joined", False),
                                              info.get("presence"))
                    self._note_client_state(name, info, verdict)
                    info["mem"] = process_memory_mb(info["pid"])
                    if self.lean_clients.get() and info["pid"] in pids and self._boosted(name):
                        if now - info.setdefault("trimmed", now) > 300 and now - info["since"] > 120 and info.get("state") == "working":
                            info["trimmed"] = now
                            slim_down_client(info["pid"])
                    info["errseen"] = info.get("errseen", 0) + 1 if (verdict[0] == "error" and verdict[2]) else 0
                    reason = None
                    if info["pid"] not in pids:
                        reason = "crashed or closed"
                    elif info["hung"] >= 3:
                        reason = "stopped responding"
                    elif info["errseen"] >= 2:  # an error window that stays open is not a working client
                        reason = f"shows an error ({verdict[1]})"
                    elif info.get("joined") and now - info["since"] > 120 and now - info.get("lastpres", 0) > self._presence_interval():
                        info["lastpres"] = now
                        acc = next((a for a in self.accounts if a["name"] == name), None)
                        if acc and acc.get("id"):
                            try:
                                presence = info["sess"].presence([acc["id"]])
                            except Exception:
                                presence = []
                            if presence:
                                info["presence"] = presence[0].get("userPresenceType")
                            if presence and presence[0].get("userPresenceType") != 2:
                                info["notin"] = info.get("notin", 0) + 1
                            else:
                                info["notin"] = 0
                            if info["notin"] >= 2:
                                reason = "left the game"
                    if reason and name in self.relaunch_on and not info.get("stopped"):
                        info["restarting"] = True
                        threading.Thread(
                            target=self._restart_account, args=(name, reason),
                            name=f"Recovery-{name}", daemon=True
                        ).start()
                    elif reason:
                        # Do not silently re-launch an account.  Keep the row
                        # visible as stopped so it can be launched explicitly.
                        info["stopped"] = True
                        self.log(f"{name}: {reason}. Auto-relaunch is off for this account, so it stays closed.")
                self._notify_state_changed(wake_monitor=False)
            except Exception as e:
                self.log(f"Watchdog error: {e}")

    def _wait_or_death(self, timeout):
        """Sleep like the monitor does, but wake at once when a tracked client disappears."""
        end = time.monotonic() + timeout
        while True:
            left = end - time.monotonic()
            if left <= 0:
                return
            if self._monitor_event.wait(min(1.5, left)) or self._shutdown_event.is_set():
                return
            if not self.tracked:
                continue
            alive = native_roblox_pids()
            if alive is None:
                continue
            for item in list(self.tracked.values()):
                if not item.get("stopped") and not item.get("restarting") and item.get("pid") not in alive:
                    return

    def _note_client_state(self, name, info, verdict):
        """Remember the client's state for the account list and report real changes once."""
        state, text, _strong = verdict
        previous = info.get("state")
        info["state"], info["state_text"] = state, text
        if state == previous:
            return
        if state == "error":
            self.log(f"{name}: Roblox shows an error - {text}.")
        elif state == "hung":
            self.log(f"{name}: Roblox is not responding.")
        elif previous in ("error", "hung") and state in ("working", "starting"):
            self.log(f"{name}: client works again.")
        self._notify_state_changed(wake_monitor=False)

    def _restart_account(self, name, reason):
        info = self.tracked.get(name)
        acc = next((a for a in self.accounts if a["name"] == name), None)
        if not info or not acc or self._action_cancel_event.is_set():
            return
        if self.tracked.get(name) is not info or info.get("stopped") or name not in self.relaunch_on:
            info["restarting"] = False
            return
        try:
            recent = [t for t in info["restarts"] if time.time() - t < 600]
            if len(recent) >= 6:
                info["stopped"] = True
                self.log(f"{name}: crashed {len(recent)} times in 10 minutes - automatic restarts stopped. "
                         "Use 'Log in again', then launch the account again.")
                return
            if len(recent) >= 3:  # unlimited restarts, but with growing pauses so a crash loop stays calm
                delay = min(300, 15 * 2 ** (len(recent) - 3))
                self.log(f"{name}: crashing often - next start in {int(delay)} s.")
                end = time.time() + delay
                while time.time() < end:
                    if (self._shutdown_event.wait(min(1.0, max(0.0, end - time.time())))
                            or self._action_cancel_event.is_set()):
                        return
                    if self.tracked.get(name) is not info or info.get("stopped"):
                        return
            info["restarts"] = recent + [time.time()]
            self.log(f"{name}: client {reason} - restarting ...")
            kill_pid(info["pid"])
            sess = info.get("sess")
            if not sess or not sess.me():
                sess = self._sessions_for([acc])[0]
            if not sess:
                info["next_try"] = time.time() + 30
                self.log(f"{name}: no valid sign-in for the relaunch - trying again in 30 s. {self._net_hint(True)}".strip())
                return
            if self._launch_one(acc, sess, info["spec"], cancel_event=self._action_cancel_event):
                try:
                    self.after(0, lambda: self.toast(f"{name} is back"))
                except (tk.TclError, RuntimeError):
                    pass
            else:
                info["fails"] = info.get("fails", 0) + 1
                wait = min(60, 15 * info["fails"])
                info["next_try"] = time.time() + wait
                self.log(f"{name}: relaunch failed - next try in {wait} s. {self._net_hint(True)}".strip())
                if info["fails"] >= 2:
                    self.log(f"{name}: restarting Microsoft Edge before the next try.")
                    kill_edge_tree(None)
                    sess2 = None
                    try:
                        sess2 = self._fresh_login(acc, self._action_cancel_event) if info["fails"] >= 3 else None
                    except Exception:
                        sess2 = None
                    if sess2:
                        info["sess"] = sess2
        except Exception as e:
            self.log(f"{name}: restart error - {e}")
            info["next_try"] = time.time() + 20
        finally:
            info["restarting"] = False
            self._notify_state_changed()

    # ---------- Profile tools ----------
    def ask_main(self, title, text):
        ev = threading.Event()
        res = {}

        def _do():
            res["v"] = messagebox.askyesno(title, text)
            ev.set()
        self.after(0, _do)
        while not ev.wait(0.3):
            if self._cancelled():  # Stop was pressed while the question was open
                return False
        return res["v"]

    def change_bio(self):
        selected = self._selected()
        description = self.e_bio.get("1.0", "end-1c").strip()
        if not selected:
            messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        if len(description) > 1000:
            messagebox.showwarning("Bio is too long", "Roblox profile descriptions are limited to 1,000 characters.")
            return
        self.log(f"Updating the profile bio for {len(selected)} selected account(s) ...")
        self._submit("Update bio", "UPDATING", self._bio_worker, selected, description)

    def _set_bio(self, acc, sess, description):
        """API attempt with retries. Returns (ok, detail, browser_can_help)."""
        detail = "unknown error"
        for attempt in range(1, 5):
            response = sess.req("POST", "https://users.roblox.com/v1/description",
                                json={"description": description})
            status = getattr(response, "status_code", None)
            if status in (200, 204):
                if self._bio_matches(sess, description):
                    return True, "", False
                detail = "Roblox changed or filtered the text"
                if attempt >= 2:
                    return False, detail, False
            else:
                try:
                    detail = response.json().get("errors", [{}])[0].get("message") or response.text[:160]
                except Exception:
                    detail = status if status is not None else "network error"
                if self._is_challenge(detail):
                    return False, detail, True
                limit = self._limit_reason(status, detail)
                if limit:
                    return False, f"limit reached - {limit}. Try again later", False
                if self._is_rate_limit(status, detail):
                    self._rate_wait("users.roblox.com")
                    continue
                if status is not None and 400 <= status < 500 and status not in (401, 403, 429):
                    return False, detail, False  # Roblox rejected the text itself
                if status == 401 and attempt == 1:
                    refreshed = self._sessions_for([acc])
                    if refreshed and refreshed[0]:
                        sess = refreshed[0]
            time.sleep(1.5 * attempt)
        return False, detail, True

    def _bio_worker(self, selected, description):
        fleet = BrowserFleet(self)
        try:
            started = time.time()
            sessions = self._sessions_for(selected)
            pairs = []
            for acc, sess in zip(selected, sessions):
                if sess:
                    self._ensure_id(acc, sess)
                    pairs.append((acc, sess))
                else:
                    self.log(f"{acc['name']}: no valid session; bio skipped.")
            if not pairs:
                return
            tick = self.jobs.ticker(len(pairs))
            fleet.prestart(pairs)

            def fast(pair):
                acc, sess = pair
                if self._cancelled():
                    tick()
                    return None
                ok, detail, use_browser = self._set_bio(acc, sess, description)
                if ok:
                    self.log(f"{acc['name']}: profile bio updated.")
                    tick()
                    return None
                if use_browser:
                    return pair
                self.log(f"{acc['name']}: could not update bio ({detail}).")
                tick()
                return None

            with ThreadPoolExecutor(max_workers=self._workers(len(pairs))) as ex:
                pending = [x for x in ex.map(fast, pairs) if x]
            for pair in pairs:
                if pair not in pending:
                    fleet.release(pair[0])
            if pending:
                self.log(f"Updating bio in {len(pending)} browser window(s) (Roblox asked for a check) ...")
                fleet.open(pending)

                def slow(pair):
                    acc, sess = pair
                    name = acc["name"]
                    browser = fleet.get(acc)
                    if browser and self._browser_attempts(
                            "bio", name, 3,
                            lambda: browser.api("https://users.roblox.com/v1/description", "POST",
                                                {"description": description}),
                            lambda: browser.ui_bio(description, acc.get("id")),
                            lambda: self._bio_matches(sess, description)):
                        self.log(f"{name}: profile bio updated.")
                    elif not self._limit_hit(name):
                        self.log(f"{name}: could not update the bio.")
                    fleet.release(acc)
                    tick()

                with ThreadPoolExecutor(max_workers=self._workers(len(pending))) as ex:
                    list(ex.map(slow, pending))
            self.log(f"Done: bio finished in {time.time() - started:.1f} s.")
        except Exception as exc:
            self.log(f"Bio update error: {exc}")
        finally:
            fleet.close()

    def change_display_name(self):
        selected = self._selected()
        new_name = self.e_display_name.get().strip()
        if not selected:
            messagebox.showinfo("No accounts selected", "Select at least one account first.")
            return
        if not 3 <= len(new_name) <= 20:
            messagebox.showwarning("Invalid display name", "Display names must be 3 to 20 characters long.")
            return
        wanted = [(account, new_name) for account in selected
                  if new_name != account.get("display", "")]
        if not wanted:
            self.log("No display-name changes are needed.")
            return
        self.log(f"Updating the display name for {len(wanted)} selected account(s) ...")
        self._submit("Change display name", "UPDATING", self._rename_worker, wanted)

    def _set_display_name(self, acc, sess, new):
        """API attempt with retries. Returns (ok, detail, browser_can_help)."""
        if not self._ensure_id(acc, sess):
            return False, "could not read the account id", True
        uid, detail = acc["id"], "unknown error"

        def error_text(resp):
            try:
                return resp.json()["errors"][0]["message"]
            except Exception:
                return resp.status_code if resp is not None else "network error"

        for attempt in range(1, 5):
            v = sess.req("GET", f"https://users.roblox.com/v1/users/{uid}/display-names/validate",
                         params={"displayName": new})
            status = getattr(v, "status_code", None)
            if status != 200:
                detail = error_text(v)
                if self._is_challenge(detail):
                    return False, detail, True
                limit = self._limit_reason(status, detail)
                if limit:
                    return False, f"limit reached - {limit}. Try again later", False
                if self._is_rate_limit(status, detail):
                    self._rate_wait("users.roblox.com")
                    continue
                if status is not None and 400 <= status < 500 and status not in (401, 403, 429):
                    return False, f"'{new}' is not allowed - {detail}", False
                time.sleep(1.5 * attempt)
                continue
            r = sess.req("PATCH", f"https://users.roblox.com/v1/users/{uid}/display-names",
                         json={"newDisplayName": new})
            status = getattr(r, "status_code", None)
            if status == 200:
                if self._display_matches(sess, uid, new):
                    return True, "", False
                detail = "Roblox did not apply the new name"
            else:
                detail = error_text(r)
                if self._is_challenge(detail):
                    return False, detail, True
                limit = self._limit_reason(status, detail)
                if limit:
                    return False, f"limit reached - {limit}. Try again later", False
                if self._is_rate_limit(status, detail):
                    self._rate_wait("users.roblox.com")
                    continue
                if status is not None and 400 <= status < 500 and status not in (401, 403, 429):
                    return False, str(detail), False
                if status == 401 and attempt == 1:
                    refreshed = self._sessions_for([acc])
                    if refreshed and refreshed[0]:
                        sess = refreshed[0]
            time.sleep(1.5 * attempt)
        return False, str(detail), True

    def _rename_worker(self, wanted):
        fleet = BrowserFleet(self)
        try:
            started = time.time()
            sessions = self._sessions_for([a for a, _ in wanted])
            jobs = []
            for (acc, new), sess in zip(wanted, sessions):
                if sess and self._ensure_id(acc, sess):
                    jobs.append((acc, new, sess))
                else:
                    self.log(f"{acc['name']}: no valid session; display name skipped.")
            if not jobs:
                return
            tick = self.jobs.ticker(len(jobs))
            fleet.prestart([(acc, sess) for acc, _, sess in jobs])

            def fast(job):
                acc, new, sess = job
                if self._cancelled():
                    tick()
                    return None
                ok, detail, use_browser = self._set_display_name(acc, sess, new)
                if ok:
                    acc["display"] = new
                    self.log(f"{acc['name']}: display name is now '{new}'.")
                    tick()
                    return None
                if use_browser:
                    return job
                self.log(f"{acc['name']}: display name not changed - {detail}")
                tick()
                return None

            with ThreadPoolExecutor(max_workers=self._workers(len(jobs))) as ex:
                pending = [x for x in ex.map(fast, jobs) if x]
            for job in jobs:
                if job not in pending:
                    fleet.release(job[0])
            if pending:
                self.log(f"Changing the display name in {len(pending)} browser window(s) (Roblox asked for a check) ...")
                fleet.open([(acc, sess) for acc, _, sess in pending])

                def slow(job):
                    acc, new, sess = job
                    name, uid = acc["name"], acc["id"]
                    browser = fleet.get(acc)
                    if browser and self._browser_attempts(
                            "display name", name, 3,
                            lambda: browser.api(f"https://users.roblox.com/v1/users/{uid}/display-names", "PATCH",
                                                {"newDisplayName": new}),
                            lambda: browser.ui_display_name(new),
                            lambda: self._display_matches(sess, uid, new)):
                        acc["display"] = new
                        self.log(f"{name}: display name is now '{new}'.")
                    elif not self._limit_hit(name):
                        self.log(f"{name}: display name could not be changed "
                                 "(Roblox allows one change per week).")
                    fleet.release(acc)
                    tick()

                with ThreadPoolExecutor(max_workers=self._workers(len(pending))) as ex:
                    list(ex.map(slow, pending))
            self._save()
            self.after(0, self._refresh_list)
            self.log(f"Done: display name finished in {time.time() - started:.1f} s.")
        except Exception as e:
            self.log(f"Display name error: {e}")
        finally:
            fleet.close()


if __name__ == "__main__":
    minimize_console_window()
    App().mainloop()
