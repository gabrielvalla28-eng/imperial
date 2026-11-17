"""
Imperial Network - TechTrack
Technician Monitoring System  (v4 - enterprise redesign)

Tkinter desktop GUI + SQLite.  No third-party packages required.

    py ImperialTechTrack.py                 run the application
    py ImperialTechTrack.py --demo          first run with sample data (only if empty)
    py ImperialTechTrack.py --db other.db   use a different database file

DATA SAFETY
  * Uses techtrack.db next to this script (same file as before).
  * Only creates NEW tables prefixed "tm_" - your existing tables are never
    touched, renamed or dropped.
  * Transactions are never deleted (a database trigger blocks it) - they are archived.
  * The history table is append-only (triggers block UPDATE and DELETE), so the
    audit trail from creation to completion can never be overwritten.
"""

import argparse
import csv
import json
import random
import re
import sqlite3
import sys
import tkinter as tk
from collections import Counter
from datetime import datetime, timedelta, date
from pathlib import Path
from tkinter import ttk, messagebox, filedialog, simpledialog

DEFAULT_DB = Path(__file__).resolve().with_name("techtrack.db")

# ------------------------------------------------------------------ design tokens
NAVY = "#14243A"
SLATE = "#334B68"
BG = "#F5F7FA"
WHITE = "#FFFFFF"
ACCENT = "#3B82F6"
GREEN = "#16A34A"
AMBER = "#F59E0B"
RED = "#DC2626"
TEXT = "#1E293B"
MUTED = "#64748B"
BORDER = "#E2E8F0"
HOVER = "#F1F5F9"
INDIGO = "#6366F1"
ORANGE = "#EA580C"
FONT = "Segoe UI"
SYMBOL = "Segoe UI Symbol"

DT_FMT = "%Y-%m-%d %H:%M:%S"
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")

JOB_TYPES = [
    "Installation", "Repair / Troubleshooting", "Reconfiguration",
    "ONU / Router Replacement", "Wi-Fi Configuration", "Site Visit",
    "Customer Complaint", "Other Technical Activity",
]
STATUSES = ["Pending", "Assigned", "In Progress", "Completed", "Rescheduled", "Failed", "Cancelled"]
PRIORITIES = ["Normal", "High", "Urgent"]
EVENT_TYPES = ["Created", "Status Change", "Reassigned", "Updated", "Note", "Archived", "Restored"]

STATUS_COLORS = {
    "Pending": AMBER, "Assigned": ACCENT, "In Progress": INDIGO, "Completed": GREEN,
    "Rescheduled": ORANGE, "Failed": RED, "Cancelled": "#94A3B8",
    "Active": GREEN, "Inactive": "#94A3B8",
}
EVENT_COLORS = {
    "Created": ACCENT, "Reassigned": INDIGO, "Updated": SLATE,
    "Note": MUTED, "Archived": MUTED, "Restored": GREEN,
}

# (column, label) - every one of these is audited when it changes
TRACKED = [
    ("customer", "Customer"), ("account_no", "Account No."), ("technician", "Technician"),
    ("job_type", "Job Type"), ("priority", "Priority"), ("concern", "Concern"),
    ("action_taken", "Action Taken"), ("remarks", "Remarks"), ("status", "Status"),
]


# ------------------------------------------------------------------ helpers
def stamp(dt=None):
    return (dt or datetime.now()).strftime(DT_FMT)


def nice(ts):
    if not ts:
        return "—"
    try:
        return datetime.strptime(ts, DT_FMT).strftime("%b %d, %Y  %I:%M %p")
    except ValueError:
        return ts


def valid_date(text):
    text = (text or "").strip()
    if DATE_RE.match(text):
        try:
            datetime.strptime(text, "%Y-%m-%d")
            return text
        except ValueError:
            pass
    return ""


def bucket(status):
    return "Ongoing" if status in ("Assigned", "In Progress") else status


def period_range(kind, ref):
    """Return (start, end_exclusive, label) as DB timestamp strings for a report period."""
    if kind == "Daily":
        s, e = ref, ref + timedelta(days=1)
        label = ref.strftime("%A, %B %d, %Y")
    elif kind == "Weekly":
        s = ref - timedelta(days=ref.weekday())
        e = s + timedelta(days=7)
        label = f"Week of {s:%b %d} – {e - timedelta(days=1):%b %d, %Y}"
    else:
        s = ref.replace(day=1)
        e = s.replace(year=s.year + 1, month=1) if s.month == 12 else s.replace(month=s.month + 1)
        label = ref.strftime("%B %Y")
    return s.strftime("%Y-%m-%d 00:00:00"), e.strftime("%Y-%m-%d 00:00:00"), label


def shift_ref(kind, ref, direction):
    if kind == "Daily":
        return ref + timedelta(days=direction)
    if kind == "Weekly":
        return ref + timedelta(days=7 * direction)
    month = ref.month - 1 + direction
    return date(ref.year + month // 12, month % 12 + 1, 1)


# ------------------------------------------------------------------ database
SCHEMA = """
CREATE TABLE IF NOT EXISTS tm_technicians(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE COLLATE NOCASE,
    phone TEXT DEFAULT '',
    active INTEGER NOT NULL DEFAULT 1
);
CREATE TABLE IF NOT EXISTS tm_transactions(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    txn_id TEXT NOT NULL UNIQUE,
    created_at TEXT NOT NULL,
    customer TEXT NOT NULL,
    account_no TEXT NOT NULL,
    technician TEXT NOT NULL DEFAULT '',
    job_type TEXT NOT NULL,
    priority TEXT NOT NULL DEFAULT 'Normal',
    concern TEXT DEFAULT '',
    action_taken TEXT DEFAULT '',
    remarks TEXT DEFAULT '',
    status TEXT NOT NULL,
    started_at TEXT,
    completed_at TEXT,
    updated_at TEXT,
    archived INTEGER NOT NULL DEFAULT 0,
    created_by TEXT DEFAULT ''
);
CREATE TABLE IF NOT EXISTS tm_history(
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    txn_id TEXT NOT NULL,
    event_at TEXT NOT NULL,
    event_type TEXT NOT NULL,
    prev_status TEXT,
    new_status TEXT,
    updated_by TEXT DEFAULT '',
    description TEXT DEFAULT '',
    changes TEXT DEFAULT '',
    snapshot TEXT DEFAULT ''
);
CREATE TABLE IF NOT EXISTS tm_settings(key TEXT PRIMARY KEY, value TEXT);
CREATE INDEX IF NOT EXISTS tm_idx_txn_status ON tm_transactions(status, archived);
CREATE INDEX IF NOT EXISTS tm_idx_txn_tech ON tm_transactions(technician);
CREATE INDEX IF NOT EXISTS tm_idx_txn_created ON tm_transactions(created_at);
CREATE INDEX IF NOT EXISTS tm_idx_hist_txn ON tm_history(txn_id);
CREATE INDEX IF NOT EXISTS tm_idx_hist_at ON tm_history(event_at);
CREATE TRIGGER IF NOT EXISTS tm_history_no_update BEFORE UPDATE ON tm_history
BEGIN SELECT RAISE(ABORT, 'History is append-only'); END;
CREATE TRIGGER IF NOT EXISTS tm_history_no_delete BEFORE DELETE ON tm_history
BEGIN SELECT RAISE(ABORT, 'History is append-only'); END;
CREATE TRIGGER IF NOT EXISTS tm_txn_no_delete BEFORE DELETE ON tm_transactions
BEGIN SELECT RAISE(ABORT, 'Transactions cannot be deleted - archive them instead'); END;
"""


class Database:
    def __init__(self, path):
        self.path = Path(path)
        self.conn = sqlite3.connect(str(self.path))
        self.conn.row_factory = sqlite3.Row
        self.conn.executescript(SCHEMA)
        self.conn.commit()

    # ---- settings
    def get_setting(self, key, default=None):
        r = self.conn.execute("SELECT value FROM tm_settings WHERE key=?", (key,)).fetchone()
        return r["value"] if r else default

    def set_setting(self, key, value):
        with self.conn:
            self.conn.execute("INSERT INTO tm_settings(key,value) VALUES(?,?) "
                              "ON CONFLICT(key) DO UPDATE SET value=excluded.value", (key, value))

    # ---- technicians
    def technician_names(self, active_only=True):
        sql = "SELECT name FROM tm_technicians"
        if active_only:
            sql += " WHERE active=1"
        return [r["name"] for r in self.conn.execute(sql + " ORDER BY name")]

    def _ensure_tech(self, name):
        if name:
            self.conn.execute("INSERT OR IGNORE INTO tm_technicians(name) VALUES(?)", (name,))

    def add_technician(self, name, phone=""):
        with self.conn:
            self.conn.execute("INSERT INTO tm_technicians(name,phone) VALUES(?,?)", (name, phone))

    def update_technician(self, name, phone=None, active=None):
        with self.conn:
            if phone is not None:
                self.conn.execute("UPDATE tm_technicians SET phone=? WHERE name=?", (phone, name))
            if active is not None:
                self.conn.execute("UPDATE tm_technicians SET active=? WHERE name=?", (int(active), name))

    def technician_stats(self):
        techs = {r["name"]: dict(r) for r in self.conn.execute("SELECT * FROM tm_technicians ORDER BY name")}
        stats = {}
        for r in self.conn.execute(
                "SELECT technician, status, COUNT(*) n, "
                "SUM(CASE WHEN started_at IS NOT NULL THEN 1 ELSE 0 END) s "
                "FROM tm_transactions WHERE archived=0 GROUP BY technician, status"):
            c = stats.setdefault(r["technician"], Counter())
            c[r["status"]] += r["n"]
            c["Started"] += r["s"] or 0
            c["Total"] += r["n"]
        out = []
        for name, t in techs.items():
            out.append((name, t["phone"], bool(t["active"]), stats.get(name, Counter())))
        if "" in stats:
            out.append(("", "", True, stats[""]))
        return out

    def tech_jobs(self, name):
        return self.conn.execute(
            "SELECT t.*, "
            "(SELECT description FROM tm_history h WHERE h.txn_id=t.txn_id ORDER BY h.id DESC LIMIT 1) last_desc, "
            "(SELECT event_at FROM tm_history h WHERE h.txn_id=t.txn_id ORDER BY h.id DESC LIMIT 1) last_at "
            "FROM tm_transactions t WHERE t.technician=? AND t.archived=0 "
            "ORDER BY t.created_at DESC, t.id DESC", (name,)).fetchall()

    # ---- transactions
    def get_txn(self, tid):
        return self.conn.execute("SELECT * FROM tm_transactions WHERE txn_id=?", (tid,)).fetchone()

    def _next_id(self, day, bump):
        prefix = "TT-" + day.replace("-", "")
        n = self.conn.execute("SELECT COUNT(*) FROM tm_transactions WHERE txn_id LIKE ?",
                              (prefix + "-%",)).fetchone()[0]
        return f"{prefix}-{n + 1 + bump:04d}"

    def _log(self, tid, etype, prev, new, by, desc, changes, snapshot, when):
        self.conn.execute(
            "INSERT INTO tm_history(txn_id,event_at,event_type,prev_status,new_status,updated_by,"
            "description,changes,snapshot) VALUES(?,?,?,?,?,?,?,?,?)",
            (tid, stamp(when), etype, prev, new, by, desc, changes, snapshot))

    def create_txn(self, d, by, note="", when=None):
        now = stamp(when)
        status = d.get("status") or "Pending"
        err = None
        for bump in range(8):
            tid = self._next_id(now[:10], bump)
            try:
                with self.conn:
                    self._ensure_tech(d.get("technician", ""))
                    self.conn.execute(
                        "INSERT INTO tm_transactions(txn_id,created_at,customer,account_no,technician,job_type,"
                        "priority,concern,action_taken,remarks,status,started_at,completed_at,updated_at,"
                        "archived,created_by) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?)",
                        (tid, now, d["customer"], d["account_no"], d.get("technician", ""), d["job_type"],
                         d.get("priority", "Normal"), d.get("concern", ""), d.get("action_taken", ""),
                         d.get("remarks", ""), status,
                         now if status == "In Progress" else None,
                         now if status == "Completed" else None, now, by))
                    row = self.get_txn(tid)
                    self._log(tid, "Created", None, status, by, note or "Transaction created", "",
                              json.dumps(dict(row)), when)
                return tid
            except sqlite3.IntegrityError as e:
                err = e
        raise err

    def update_txn(self, tid, changes, by, note="", when=None):
        row = self.get_txn(tid)
        if row is None:
            raise KeyError(tid)
        now = stamp(when)
        diff = {}
        for key, _ in TRACKED:
            if key in changes and (row[key] or "") != (changes[key] or ""):
                diff[key] = (row[key] or "", changes[key] or "")
        if not diff and not note:
            return False
        prev = row["status"]
        new = diff["status"][1] if "status" in diff else prev
        sets = {k: v[1] for k, v in diff.items()}
        if new != prev:
            if new == "In Progress" and not row["started_at"]:
                sets["started_at"] = now
            if new == "Completed":
                sets["completed_at"] = now
            elif prev == "Completed":
                sets["completed_at"] = None
        sets["updated_at"] = now
        if "status" in diff:
            etype = "Status Change"
        elif "technician" in diff:
            etype = "Reassigned"
        elif diff:
            etype = "Updated"
        else:
            etype = "Note"
        labels = dict(TRACKED)
        parts = []
        for k, (o, n) in diff.items():
            if k in ("concern", "action_taken", "remarks"):
                parts.append(f"{labels[k]} edited")
            else:
                parts.append(f"{labels[k]}: {o or '—'} → {n or '—'}")
        changes_txt = "; ".join(parts)
        with self.conn:
            if "technician" in sets:
                self._ensure_tech(sets["technician"])
            cols = ", ".join(f"{k}=?" for k in sets)
            self.conn.execute(f"UPDATE tm_transactions SET {cols} WHERE txn_id=?", (*sets.values(), tid))
            # snapshot = the record exactly as it was BEFORE this update
            self._log(tid, etype, prev, new, by, note or changes_txt or "Updated", changes_txt,
                      json.dumps(dict(row)), when)
        return True

    def set_archived(self, tid, flag, by, when=None):
        row = self.get_txn(tid)
        with self.conn:
            self.conn.execute("UPDATE tm_transactions SET archived=?, updated_at=? WHERE txn_id=?",
                              (int(flag), stamp(when), tid))
            self._log(tid, "Archived" if flag else "Restored", row["status"], row["status"], by,
                      "Moved to archive (history preserved)" if flag else "Restored from archive",
                      "", json.dumps(dict(row)), when)

    def find_open_duplicate(self, account_no, job_type):
        return self.conn.execute(
            "SELECT txn_id FROM tm_transactions WHERE archived=0 AND lower(account_no)=lower(?) "
            "AND job_type=? AND status NOT IN ('Completed','Cancelled') LIMIT 1",
            (account_no, job_type)).fetchone()

    def search(self, text="", field="All", technician="", job_type="", status="",
               date_from="", date_to="", archived=0):
        sql, args = "SELECT * FROM tm_transactions WHERE archived=?", [archived]
        cols = {"All": ["txn_id", "customer", "account_no", "technician"], "Customer": ["customer"],
                "Account No.": ["account_no"], "Technician": ["technician"], "Transaction ID": ["txn_id"]}
        if text:
            sql += " AND (" + " OR ".join(f"{c} LIKE ?" for c in cols.get(field, cols["All"])) + ")"
            args += [f"%{text}%"] * len(cols.get(field, cols["All"]))
        if technician == "(Unassigned)":
            sql += " AND technician=''"
        elif technician:
            sql += " AND technician=?"
            args.append(technician)
        if job_type:
            sql += " AND job_type=?"
            args.append(job_type)
        if status:
            sql += " AND status=?"
            args.append(status)
        if date_from:
            sql += " AND created_at>=?"
            args.append(date_from + " 00:00:00")
        if date_to:
            nxt = datetime.strptime(date_to, "%Y-%m-%d") + timedelta(days=1)
            sql += " AND created_at<?"
            args.append(nxt.strftime("%Y-%m-%d 00:00:00"))
        return self.conn.execute(sql + " ORDER BY created_at DESC, id DESC", args).fetchall()

    def count_txns(self, archived=0):
        return self.conn.execute("SELECT COUNT(*) FROM tm_transactions WHERE archived=?", (archived,)).fetchone()[0]

    def status_counts(self):
        c = Counter()
        for r in self.conn.execute("SELECT status, COUNT(*) n FROM tm_transactions WHERE archived=0 GROUP BY status"):
            c[r["status"]] = r["n"]
        return c

    def type_counts(self):
        return [(r["job_type"], r["n"]) for r in self.conn.execute(
            "SELECT job_type, COUNT(*) n FROM tm_transactions WHERE archived=0 "
            "GROUP BY job_type ORDER BY n DESC")]

    # ---- history
    def history(self, tid):
        return self.conn.execute("SELECT * FROM tm_history WHERE txn_id=? ORDER BY id", (tid,)).fetchall()

    def history_search(self, text="", etype="", date_from="", date_to="", limit=2000):
        sql = ("SELECT h.*, t.customer, t.account_no, t.technician FROM tm_history h "
               "LEFT JOIN tm_transactions t ON t.txn_id=h.txn_id WHERE 1=1")
        args = []
        if text:
            sql += (" AND (h.txn_id LIKE ? OR t.customer LIKE ? OR t.account_no LIKE ? "
                    "OR h.description LIKE ? OR h.updated_by LIKE ?)")
            args += [f"%{text}%"] * 5
        if etype:
            sql += " AND h.event_type=?"
            args.append(etype)
        if date_from:
            sql += " AND h.event_at>=?"
            args.append(date_from + " 00:00:00")
        if date_to:
            nxt = datetime.strptime(date_to, "%Y-%m-%d") + timedelta(days=1)
            sql += " AND h.event_at<?"
            args.append(nxt.strftime("%Y-%m-%d 00:00:00"))
        return self.conn.execute(sql + " ORDER BY h.id DESC LIMIT ?", (*args, limit)).fetchall()

    # ---- reports
    def report(self, kind, ref):
        """Activity report. Jobs 'handled' = jobs with any (non-archive) activity in the period.
        Statuses are as at the END of the period, rebuilt from the audit trail."""
        start, end, label = period_range(kind, ref)
        events = self.conn.execute(
            "SELECT txn_id,event_at,event_type,new_status FROM tm_history WHERE event_at < ? ORDER BY id",
            (end,)).fetchall()
        last, touched, created, in_range = {}, set(), set(), []
        for e in events:
            last[e["txn_id"]] = e["new_status"]
            if e["event_at"] >= start and e["event_type"] not in ("Archived", "Restored"):
                touched.add(e["txn_id"])
                in_range.append(e["txn_id"])
                if e["event_type"] == "Created":
                    created.add(e["txn_id"])
        meta = {r["txn_id"]: (r["technician"] or "(Unassigned)", r["job_type"])
                for r in self.conn.execute("SELECT txn_id,technician,job_type FROM tm_transactions")}

        def build(idx):
            groups = {}
            for tid in touched:
                g = groups.setdefault(meta.get(tid, ("?", "?"))[idx], Counter())
                g["Handled"] += 1
                g[bucket(last[tid])] += 1
            for tid in in_range:
                groups.setdefault(meta.get(tid, ("?", "?"))[idx], Counter())["Updates"] += 1
            return [[k, g["Handled"], g["Completed"], g["Ongoing"], g["Pending"], g["Rescheduled"],
                     g["Failed"], g["Cancelled"], g["Updates"]]
                    for k, g in sorted(groups.items(), key=lambda kv: (-kv[1]["Handled"], kv[0]))]

        tot = Counter(bucket(last[t]) for t in touched)
        kpis = {"Handled": len(touched), "Created": len(created), "Completed": tot["Completed"],
                "Ongoing": tot["Ongoing"], "Pending": tot["Pending"], "Rescheduled": tot["Rescheduled"],
                "Failed": tot["Failed"], "Cancelled": tot["Cancelled"], "Updates": len(in_range)}
        return {"label": label, "kpis": kpis, "by_tech": build(0), "by_type": build(1)}


# ------------------------------------------------------------------ styling
def setup_style(root):
    root.option_add("*Font", (FONT, 10))
    root.option_add("*TCombobox*Listbox.font", (FONT, 10))
    root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
    s = ttk.Style(root)
    s.theme_use("clam")
    s.configure(".", font=(FONT, 10), background=BG, foreground=TEXT)
    s.configure("Treeview", background=WHITE, fieldbackground=WHITE, foreground=TEXT,
                rowheight=34, borderwidth=0, font=(FONT, 10))
    s.layout("Treeview", [("Treeview.treearea", {"sticky": "nswe"})])
    s.configure("Treeview.Heading", background="#F8FAFC", foreground=MUTED, relief="flat",
                font=(FONT, 9, "bold"), padding=(10, 9), borderwidth=0)
    s.map("Treeview", background=[("selected", "#DBEAFE")], foreground=[("selected", NAVY)])
    s.map("Treeview.Heading", background=[("active", "#EEF2F7")])
    s.configure("TEntry", fieldbackground=WHITE, foreground=TEXT, bordercolor=BORDER,
                lightcolor=BORDER, darkcolor=BORDER, padding=6)
    s.map("TEntry", bordercolor=[("focus", ACCENT)], lightcolor=[("focus", ACCENT)],
          darkcolor=[("focus", ACCENT)])
    s.configure("TCombobox", fieldbackground=WHITE, background=WHITE, foreground=TEXT, arrowcolor=MUTED,
                bordercolor=BORDER, lightcolor=BORDER, darkcolor=BORDER, padding=6)
    s.map("TCombobox", fieldbackground=[("readonly", WHITE)], selectbackground=[("readonly", WHITE)],
          selectforeground=[("readonly", TEXT)], bordercolor=[("focus", ACCENT)],
          lightcolor=[("focus", ACCENT)], darkcolor=[("focus", ACCENT)])
    for o in ("Vertical", "Horizontal"):
        s.configure(f"{o}.TScrollbar", background="#CBD5E1", troughcolor=WHITE, bordercolor=WHITE,
                    arrowcolor=WHITE, lightcolor="#CBD5E1", darkcolor="#CBD5E1", relief="flat", arrowsize=12)
        s.map(f"{o}.TScrollbar", background=[("active", "#94A3B8")])


_DOTS = {}


def dot(status):
    """Small coloured status indicator used in table rows."""
    color = STATUS_COLORS.get(status, MUTED)
    if color not in _DOTS:
        img = tk.PhotoImage(width=14, height=14)
        for x in range(14):
            for y in range(14):
                if (x - 6.5) ** 2 + (y - 6.5) ** 2 <= 4.8 ** 2:
                    img.put(color, (x, y))
        _DOTS[color] = img
    return _DOTS[color]


# ------------------------------------------------------------------ widgets
class Btn(tk.Label):
    STYLES = {
        "primary": (ACCENT, "#2563EB", WHITE, ACCENT),
        "secondary": (WHITE, HOVER, TEXT, BORDER),
        "danger": (WHITE, "#FEF2F2", RED, "#FECACA"),
    }

    def __init__(self, parent, text, command=None, kind="secondary"):
        bg, hov, fg, bd = self.STYLES[kind]
        super().__init__(parent, text=text, bg=bg, fg=fg, padx=14, pady=7, cursor="hand2",
                         font=(FONT, 10, "bold" if kind == "primary" else "normal"),
                         highlightthickness=1, highlightbackground=bd, highlightcolor=bd)
        self._bg, self._hov, self.command = bg, hov, command
        self.bind("<Enter>", lambda e: self.configure(bg=self._hov))
        self.bind("<Leave>", lambda e: self.configure(bg=self._bg))
        self.bind("<ButtonRelease-1>", self._click)

    def _click(self, e):
        if self.command and 0 <= e.x < self.winfo_width() and 0 <= e.y < self.winfo_height():
            self.command()


def make_card(parent, **kw):
    return tk.Frame(parent, bg=WHITE, highlightthickness=1, highlightbackground=BORDER,
                    highlightcolor=BORDER, **kw)


def card_header(card, title, subtitle=""):
    f = tk.Frame(card, bg=WHITE)
    f.pack(fill="x", padx=18, pady=(14, 8))
    tk.Label(f, text=title, font=(FONT, 11, "bold"), bg=WHITE, fg=TEXT).pack(side="left")
    if subtitle:
        tk.Label(f, text=subtitle, font=(FONT, 9), bg=WHITE, fg=MUTED).pack(side="left", padx=(10, 0))
    return f


def text_box(parent, height=3):
    t = tk.Text(parent, height=height, wrap="word", font=(FONT, 10), relief="flat", bg=WHITE, fg=TEXT,
                highlightthickness=1, highlightbackground=BORDER, highlightcolor=ACCENT,
                padx=8, pady=6, insertbackground=TEXT)
    t.bind("<Tab>", lambda e: (e.widget.tk_focusNext().focus(), "break")[1])
    return t


def small_label(parent, text, bg=WHITE):
    return tk.Label(parent, text=text, font=(FONT, 9), fg=MUTED, bg=bg, anchor="w")


class KpiCard(tk.Frame):
    def __init__(self, parent, title, color):
        super().__init__(parent, bg=WHITE, highlightthickness=1, highlightbackground=BORDER)
        tk.Frame(self, bg=color, height=3).pack(fill="x")
        tk.Label(self, text=title.upper(), font=(FONT, 8, "bold"), fg=MUTED, bg=WHITE).pack(
            anchor="w", padx=16, pady=(12, 0))
        self.value = tk.Label(self, text="0", font=(FONT, 26, "bold"), fg=TEXT, bg=WHITE)
        self.value.pack(anchor="w", padx=16)
        self.sub = tk.Label(self, text=" ", font=(FONT, 9), fg=MUTED, bg=WHITE)
        self.sub.pack(anchor="w", padx=16, pady=(0, 12))

    def set(self, value, sub=" "):
        self.value.configure(text=str(value))
        self.sub.configure(text=sub or " ")


class BarList(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent, bg=WHITE)
        self.columnconfigure(1, weight=1)

    def set(self, items):
        for w in self.winfo_children():
            w.destroy()
        top = max([v for _, v, _ in items] + [1])
        for i, (label, value, color) in enumerate(items):
            tk.Label(self, text=label, font=(FONT, 10), bg=WHITE, fg=TEXT, anchor="w", width=24).grid(
                row=i, column=0, sticky="w", pady=5)
            cv = tk.Canvas(self, height=8, bg=WHITE, highlightthickness=0)
            cv.grid(row=i, column=1, sticky="ew", padx=8)
            cv.bind("<Configure>", lambda e, c=cv, f=value / top, col=color: self._draw(c, f, col))
            tk.Label(self, text=str(value), font=(FONT, 10, "bold"), bg=WHITE, fg=TEXT, width=4,
                     anchor="e").grid(row=i, column=2, sticky="e")

    @staticmethod
    def _draw(cv, frac, color):
        cv.delete("all")
        w = cv.winfo_width()
        cv.create_rectangle(0, 0, w, 8, fill="#EEF2F7", width=0)
        if frac > 0:
            cv.create_rectangle(0, 0, max(int(w * frac), 4), 8, fill=color, width=0)


class DataTable(tk.Frame):
    """Treeview wrapper. columns = [(key, title, width, anchor)]. Rows = [(iid, values, status|None)]."""

    def __init__(self, parent, columns, dots=False, on_open=None, height=10):
        super().__init__(parent, bg=WHITE)
        self.use_dots, self.on_open = dots, on_open
        self.tree = ttk.Treeview(self, columns=[c[0] for c in columns], selectmode="browse", height=height,
                                 show="tree headings" if dots else "headings")
        if dots:
            self.tree.column("#0", width=36, minwidth=36, stretch=False, anchor="center")
            self.tree.heading("#0", text="")
        for key, title, width, anchor in columns:
            self.tree.heading(key, text=title, anchor="w" if anchor == "w" else "center")
            self.tree.column(key, width=width, minwidth=50, anchor=anchor, stretch=True)
        vs = ttk.Scrollbar(self, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vs.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        vs.grid(row=0, column=1, sticky="ns")
        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)
        self.tree.tag_configure("odd", background="#F8FAFC")
        self.empty = tk.Label(self, text="No records found", font=(FONT, 10), fg=MUTED, bg=WHITE)
        self.tree.bind("<Double-1>", self._dbl)
        self.tree.bind("<Return>", lambda e: self._open(self.selected()))

    def _dbl(self, e):
        self._open(self.tree.identify_row(e.y))

    def _open(self, iid):
        if iid and self.on_open:
            self.on_open(iid)

    def selected(self):
        sel = self.tree.selection()
        return sel[0] if sel else None

    def load(self, rows):
        sel = self.selected()
        self.tree.delete(*self.tree.get_children())
        for i, (iid, values, status) in enumerate(rows):
            kw = {"image": dot(status)} if self.use_dots else {}
            self.tree.insert("", "end", iid=iid, values=values, tags=("odd",) if i % 2 else (), **kw)
        if sel and self.tree.exists(sel):
            self.tree.selection_set(sel)
        if rows:
            self.empty.place_forget()
        else:
            self.empty.place(relx=.5, rely=.55, anchor="center")


class Modal(tk.Toplevel):
    def __init__(self, app, title):
        super().__init__(app.root)
        self.app = app
        self.title(title)
        self.configure(bg=WHITE)
        self.transient(app.root)
        self.bind("<Escape>", lambda e: self.destroy())

    def present(self, modal=True):
        self.update_idletasks()
        r = self.app.root
        w, h = self.winfo_reqwidth(), self.winfo_reqheight()
        x = r.winfo_rootx() + max((r.winfo_width() - w) // 2, 0)
        y = r.winfo_rooty() + max((r.winfo_height() - h) // 3, 0)
        self.geometry(f"+{x}+{y}")
        if modal:
            try:
                self.wait_visibility()
                self.grab_set()
            except tk.TclError:
                pass
        self.focus_set()


# ------------------------------------------------------------------ dialogs
class TxnForm(Modal):
    def __init__(self, app, txn=None, on_saved=None):
        super().__init__(app, "Update Transaction" if txn else "New Transaction")
        self.txn, self.on_saved, self._loading = txn, on_saved, True
        body = tk.Frame(self, bg=WHITE, padx=26, pady=22)
        body.pack(fill="both", expand=True)
        body.columnconfigure((0, 1), weight=1, uniform="c", minsize=280)
        tk.Label(body, text=f"Update {txn['txn_id']}" if txn else "New Transaction",
                 font=(FONT, 16, "bold"), bg=WHITE, fg=TEXT).grid(row=0, column=0, columnspan=2, sticky="w")
        tk.Label(body, text="Every change is saved to the permanent history timeline." if txn else
                 "A unique Transaction ID is generated automatically.", font=(FONT, 9), bg=WHITE,
                 fg=MUTED).grid(row=1, column=0, columnspan=2, sticky="w", pady=(2, 14))

        self.v = {k: tk.StringVar() for k in ("customer", "account_no", "technician", "job_type",
                                              "priority", "status")}
        techs = ["(Unassigned)"] + app.db.technician_names()
        if txn and txn["technician"] and txn["technician"] not in techs:
            techs.append(txn["technician"])

        def lab(text, r, c, span=1):
            small_label(body, text).grid(row=r, column=c, columnspan=span, sticky="w",
                                         padx=(0 if c == 0 else 8, 0), pady=(8, 2))

        def put(w, r, c, span=1):
            w.grid(row=r, column=c, columnspan=span, sticky="ew", padx=(0 if c == 0 else 8, 0))
            return w

        lab("Customer Name *", 2, 0)
        lab("Account Number *", 2, 1)
        self.e_customer = put(ttk.Entry(body, textvariable=self.v["customer"]), 3, 0)
        put(ttk.Entry(body, textvariable=self.v["account_no"]), 3, 1)
        lab("Technician Assigned", 4, 0)
        lab("Job Type *", 4, 1)
        put(ttk.Combobox(body, textvariable=self.v["technician"], values=techs, state="readonly"), 5, 0)
        put(ttk.Combobox(body, textvariable=self.v["job_type"], values=JOB_TYPES, state="readonly"), 5, 1)
        lab("Priority", 6, 0)
        lab("Job Status", 6, 1)
        put(ttk.Combobox(body, textvariable=self.v["priority"], values=PRIORITIES, state="readonly"), 7, 0)
        put(ttk.Combobox(body, textvariable=self.v["status"], values=STATUSES, state="readonly"), 7, 1)
        lab("Problem / Customer Concern", 8, 0, 2)
        self.t_concern = put(text_box(body, 3), 9, 0, 2)
        lab("Action Taken", 10, 0, 2)
        self.t_action = put(text_box(body, 3), 11, 0, 2)
        lab("Solution / Remarks", 12, 0, 2)
        self.t_remarks = put(text_box(body, 3), 13, 0, 2)
        lab("What happened? (recorded in history)" if txn else "Initial note (optional)", 14, 0, 2)
        self.note = ttk.Entry(body)
        put(self.note, 15, 0, 2)

        btns = tk.Frame(body, bg=WHITE)
        btns.grid(row=16, column=0, columnspan=2, sticky="e", pady=(20, 0))
        Btn(btns, "Cancel", self.destroy).pack(side="left", padx=(0, 8))
        Btn(btns, "Save Changes" if txn else "Create Transaction", self.save, "primary").pack(side="left")

        if txn:
            for k in self.v:
                self.v[k].set(txn[k] or ("(Unassigned)" if k == "technician" else ""))
            self.t_concern.insert("1.0", txn["concern"] or "")
            self.t_action.insert("1.0", txn["action_taken"] or "")
            self.t_remarks.insert("1.0", txn["remarks"] or "")
        else:
            self.v["technician"].set("(Unassigned)")
            self.v["priority"].set("Normal")
            self.v["status"].set("Pending")
            self.v["technician"].trace_add("write", self._tech_changed)
        self._loading = False
        self.present()
        self.e_customer.focus_set()

    def _tech_changed(self, *a):
        if not self._loading and not self.txn and self.v["status"].get() == "Pending" \
                and self.v["technician"].get() not in ("", "(Unassigned)"):
            self.v["status"].set("Assigned")

    def save(self):
        d = {k: self.v[k].get().strip() for k in self.v}
        if d["technician"] == "(Unassigned)":
            d["technician"] = ""
        d["concern"] = self.t_concern.get("1.0", "end").strip()
        d["action_taken"] = self.t_action.get("1.0", "end").strip()
        d["remarks"] = self.t_remarks.get("1.0", "end").strip()
        note = self.note.get().strip()

        def bad(msg):
            messagebox.showwarning("Check this record", msg, parent=self)

        if not d["customer"] or not d["account_no"]:
            return bad("Customer name and account number are required.")
        if not d["job_type"]:
            return bad("Please choose a job type.")
        if d["status"] in ("Assigned", "In Progress") and not d["technician"]:
            return bad(f"Assign a technician before setting the status to {d['status']}.")
        if d["status"] == "Completed" and not (d["action_taken"] or d["remarks"]):
            return bad("Add the Action Taken or Solution / Remarks before marking this job Completed.")
        changed = (not self.txn) or d["status"] != self.txn["status"]
        if d["status"] in ("Failed", "Rescheduled", "Cancelled") and changed and not note:
            return bad(f"Please describe what happened (reason for {d['status']}).")
        db = self.app.db
        try:
            if self.txn:
                tid = self.txn["txn_id"]
                if not db.update_txn(tid, d, self.app.user, note):
                    return bad("Nothing was changed.")
            else:
                dup = db.find_open_duplicate(d["account_no"], d["job_type"])
                if dup and not messagebox.askyesno(
                        "Possible duplicate",
                        f"{dup['txn_id']} is already open for this account and job type.\n\n"
                        "Create another transaction anyway?", parent=self):
                    return
                tid = db.create_txn(d, self.app.user, note)
        except sqlite3.Error as e:
            return messagebox.showerror("Could not save", str(e), parent=self)
        self.destroy()
        self.app.refresh_all()
        if self.on_saved:
            self.on_saved(tid)


class TechDialog(Modal):
    def __init__(self, app, name=None):
        super().__init__(app, "Edit Technician" if name else "Add Technician")
        self.orig = name
        body = tk.Frame(self, bg=WHITE, padx=26, pady=22)
        body.pack()
        tk.Label(body, text=self.title(), font=(FONT, 15, "bold"), bg=WHITE, fg=TEXT).grid(
            row=0, column=0, sticky="w", pady=(0, 10))
        small_label(body, "Full name").grid(row=1, column=0, sticky="w")
        self.name = ttk.Entry(body, width=36)
        self.name.grid(row=2, column=0, sticky="ew")
        small_label(body, "Phone").grid(row=3, column=0, sticky="w", pady=(10, 0))
        self.phone = ttk.Entry(body, width=36)
        self.phone.grid(row=4, column=0, sticky="ew")
        if name:
            r = app.db.conn.execute("SELECT * FROM tm_technicians WHERE name=?", (name,)).fetchone()
            self.name.insert(0, name)
            self.name.state(["disabled"])
            self.phone.insert(0, r["phone"] or "")
            small_label(body, "Names are locked so history stays consistent.").grid(row=5, column=0, sticky="w")
        b = tk.Frame(body, bg=WHITE)
        b.grid(row=6, column=0, sticky="e", pady=(18, 0))
        Btn(b, "Cancel", self.destroy).pack(side="left", padx=(0, 8))
        Btn(b, "Save", self.save, "primary").pack(side="left")
        self.present()
        (self.phone if name else self.name).focus_set()

    def save(self):
        name, phone = self.name.get().strip(), self.phone.get().strip()
        if not name:
            return messagebox.showwarning("Name required", "Enter the technician's name.", parent=self)
        try:
            if self.orig:
                self.app.db.update_technician(self.orig, phone=phone)
            else:
                self.app.db.add_technician(name, phone)
        except sqlite3.IntegrityError:
            return messagebox.showwarning("Duplicate", "A technician with that name already exists.", parent=self)
        self.destroy()
        self.app.refresh_all()


class TxnDetail(Modal):
    """Transaction detail view with full history timeline."""

    def __init__(self, app, tid):
        super().__init__(app, f"Transaction {tid}")
        self.tid = tid
        self.geometry("1040x720")
        self.minsize(900, 600)
        self._tags = set()
        app.detail_windows.add(self)
        self.bind("<Destroy>", lambda e: app.detail_windows.discard(self) if e.widget is self else None)
        self.render()
        self.update_idletasks()
        r = app.root
        self.geometry(f"+{r.winfo_rootx() + 60}+{r.winfo_rooty() + 30}")
        self.focus_set()

    def ctag(self, widget, color, bold=False):
        name = f"c{color.lstrip('#')}{'b' if bold else ''}"
        if name not in self._tags:
            widget.tag_configure(name, foreground=color, font=(FONT, 10, "bold" if bold else "normal"))
            self._tags.add(name)
        return name

    def render(self):
        for w in self.winfo_children():
            w.destroy()
        self._tags.clear()
        t = self.app.db.get_txn(self.tid)
        if t is None:
            return self.destroy()
        root = tk.Frame(self, bg=BG, padx=22, pady=18)
        root.pack(fill="both", expand=True)
        root.columnconfigure(0, weight=3, uniform="d")
        root.columnconfigure(1, weight=2, uniform="d")
        root.rowconfigure(1, weight=1)

        head = make_card(root)
        head.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 14))
        hi = tk.Frame(head, bg=WHITE, padx=20, pady=14)
        hi.pack(fill="x")
        tk.Label(hi, text=t["txn_id"], font=(FONT, 18, "bold"), bg=WHITE, fg=TEXT).pack(side="left")
        tk.Label(hi, text=t["status"], font=(FONT, 9, "bold"), bg=STATUS_COLORS.get(t["status"], MUTED),
                 fg=WHITE, padx=10, pady=3).pack(side="left", padx=14)
        if t["archived"]:
            tk.Label(hi, text="ARCHIVED", font=(FONT, 9, "bold"), bg=HOVER, fg=MUTED, padx=10, pady=3,
                     highlightthickness=1, highlightbackground=BORDER).pack(side="left")
        tk.Label(hi, text=f"{t['job_type']}  ·  {t['customer']}", font=(FONT, 10), bg=WHITE, fg=MUTED).pack(
            side="right")

        left = make_card(root)
        left.grid(row=1, column=0, sticky="nsew", padx=(0, 7))
        card_header(left, "Transaction Details")
        grid = tk.Frame(left, bg=WHITE)
        grid.pack(fill="x", padx=18)
        grid.columnconfigure((1, 3), weight=1, uniform="v")
        rows = [("Date & Time", nice(t["created_at"])), ("Account No.", t["account_no"]),
                ("Customer", t["customer"]), ("Technician", t["technician"] or "Unassigned"),
                ("Job Type", t["job_type"]), ("Priority", t["priority"]),
                ("Started", nice(t["started_at"])), ("Completed", nice(t["completed_at"])),
                ("Last Updated", nice(t["updated_at"])), ("Created By", t["created_by"] or "—")]
        for i, (k, v) in enumerate(rows):
            r, c = divmod(i, 2)
            small_label(grid, k).grid(row=r * 2, column=c * 2, sticky="w", padx=(0 if c == 0 else 14, 0), pady=(8, 0))
            tk.Label(grid, text=v, font=(FONT, 10), bg=WHITE, fg=TEXT, anchor="w").grid(
                row=r * 2 + 1, column=c * 2, sticky="w", padx=(0 if c == 0 else 14, 0))
        for title, val in (("Problem / Customer Concern", t["concern"]), ("Action Taken", t["action_taken"]),
                           ("Solution / Remarks", t["remarks"])):
            small_label(left, title).pack(anchor="w", padx=18, pady=(14, 0))
            tk.Label(left, text=val or "—", font=(FONT, 10), bg=WHITE, fg=TEXT, justify="left", anchor="w",
                     wraplength=470).pack(anchor="w", padx=18, fill="x")

        right = make_card(root)
        right.grid(row=1, column=1, sticky="nsew", padx=(7, 0))
        n = len(self.app.db.history(self.tid))
        card_header(right, "History Timeline", f"{n} event{'s' if n != 1 else ''} · permanent record")
        wrap = tk.Frame(right, bg=WHITE)
        wrap.pack(fill="both", expand=True, padx=(18, 6), pady=(0, 12))
        tl = tk.Text(wrap, wrap="word", relief="flat", bg=WHITE, fg=TEXT, font=(FONT, 10), highlightthickness=0,
                     cursor="arrow", padx=0, pady=2, spacing1=1)
        sb = ttk.Scrollbar(wrap, orient="vertical", command=tl.yview)
        tl.configure(yscrollcommand=sb.set)
        tl.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        tl.tag_configure("title", font=(FONT, 10, "bold"))
        tl.tag_configure("muted", foreground=MUTED, font=(FONT, 9))
        tl.tag_configure("ind", lmargin1=22, lmargin2=22)
        tl.tag_configure("small", foreground=MUTED, font=(FONT, 9, "italic"))
        for h in self.app.db.history(self.tid):
            color = STATUS_COLORS.get(h["new_status"], ACCENT) if h["event_type"] == "Status Change" \
                else EVENT_COLORS.get(h["event_type"], MUTED)
            tl.insert("end", "● ", self.ctag(tl, color, True))
            tl.insert("end", h["event_type"], "title")
            tl.insert("end", f"   {nice(h['event_at'])}\n", "muted")
            if h["prev_status"] and h["prev_status"] != h["new_status"]:
                tl.insert("end", f"{h['prev_status']}  →  {h['new_status']}\n",
                          ("ind", self.ctag(tl, STATUS_COLORS.get(h["new_status"], MUTED), True)))
            elif h["event_type"] == "Created":
                tl.insert("end", f"Started as {h['new_status']}\n", ("ind", "muted"))
            tl.insert("end", f"by {h['updated_by'] or 'unknown'}\n", ("ind", "muted"))
            if h["description"]:
                tl.insert("end", h["description"] + "\n", "ind")
            if h["changes"] and h["changes"] != h["description"]:
                tl.insert("end", h["changes"] + "\n", ("ind", "small"))
            tl.insert("end", "\n")
        tl.configure(state="disabled")
        tl.see("end")

        bar = tk.Frame(root, bg=BG)
        bar.grid(row=2, column=0, columnspan=2, sticky="e", pady=(14, 0))
        Btn(bar, "Close", self.destroy).pack(side="right")
        if t["archived"]:
            Btn(bar, "Restore from Archive", lambda: self.app.archive(self.tid, False, self), "secondary").pack(
                side="right", padx=8)
        else:
            Btn(bar, "Archive", lambda: self.app.archive(self.tid, True, self), "danger").pack(side="right", padx=8)
            Btn(bar, "Update / Add Remark", lambda: TxnForm(self.app, self.app.db.get_txn(self.tid)),
                "primary").pack(side="right")


# ------------------------------------------------------------------ pages
class Page(tk.Frame):
    title = ""
    subtitle = ""

    def __init__(self, parent, app):
        super().__init__(parent, bg=BG)
        self.app = app
        self._after = None

    def header(self, *buttons):
        f = tk.Frame(self, bg=BG)
        f.pack(fill="x", pady=(0, 14))
        tk.Label(f, text=self.subtitle, font=(FONT, 10), fg=MUTED, bg=BG).pack(side="left")
        for text, cmd, kind in reversed(buttons):
            Btn(f, text, cmd, kind).pack(side="right", padx=(8, 0))
        return f

    def schedule(self, *a):
        if self._after:
            self.after_cancel(self._after)
        self._after = self.after(180, self.refresh)

    def refresh(self):
        pass


def txn_row(r):
    return (r["txn_id"], (r["txn_id"], nice(r["created_at"]), r["customer"], r["account_no"],
                          r["technician"] or "Unassigned", r["job_type"], r["status"], nice(r["completed_at"])),
            r["status"])


TXN_COLS = [("id", "Transaction ID", 112, "w"), ("dt", "Date & Time", 140, "w"), ("customer", "Customer", 140, "w"),
            ("acct", "Account No.", 100, "w"), ("tech", "Technician", 115, "w"), ("type", "Job Type", 150, "w"),
            ("status", "Status", 90, "w"), ("done", "Completed", 140, "w")]


class DashboardPage(Page):
    title = "Dashboard"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Live overview of all technician jobs and activity"
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)
        kp = tk.Frame(self, bg=BG)
        kp.grid(row=0, column=0, sticky="ew")
        self.k = {}
        defs = [("total", "Total Jobs", SLATE), ("completed", "Completed", GREEN), ("ongoing", "Ongoing", ACCENT),
                ("pending", "Pending", AMBER), ("cancelled", "Cancelled", RED)]
        for i, (key, title, color) in enumerate(defs):
            kp.columnconfigure(i, weight=1, uniform="k")
            self.k[key] = KpiCard(kp, title, color)
            self.k[key].grid(row=0, column=i, sticky="nsew", padx=(0 if i == 0 else 7, 0 if i == 4 else 7))

        mid = tk.Frame(self, bg=BG)
        mid.grid(row=1, column=0, sticky="ew", pady=14)
        mid.columnconfigure(0, weight=3, uniform="m")
        mid.columnconfigure(1, weight=2, uniform="m")
        c1 = make_card(mid)
        c1.grid(row=0, column=0, sticky="nsew", padx=(0, 7))
        card_header(c1, "Activity Summary", "Daily · Weekly · Monthly")
        self.summary = DataTable(c1, [("p", "Period", 130, "w"), ("h", "Jobs Handled", 100, "center"),
                                      ("c", "Created", 80, "center"), ("d", "Completed", 90, "center"),
                                      ("x", "Cancelled", 90, "center"), ("u", "Updates", 80, "center")], height=3)
        self.summary.pack(fill="x", padx=1, pady=(0, 1))
        c2 = make_card(mid)
        c2.grid(row=0, column=1, sticky="nsew", padx=(7, 0))
        card_header(c2, "Status Breakdown")
        self.bars = BarList(c2)
        self.bars.pack(fill="x", padx=18, pady=(0, 12))

        bot = tk.Frame(self, bg=BG)
        bot.grid(row=2, column=0, sticky="nsew")
        bot.rowconfigure(0, weight=1)
        bot.columnconfigure(0, weight=3, uniform="b")
        bot.columnconfigure(1, weight=2, uniform="b")
        c3 = make_card(bot)
        c3.grid(row=0, column=0, sticky="nsew", padx=(0, 7))
        card_header(c3, "Recent Activity", "double-click to open")
        self.recent = DataTable(c3, [("t", "Time", 140, "w"), ("id", "Transaction", 112, "w"),
                                     ("e", "Event", 100, "w"), ("d", "Details", 250, "w"), ("b", "By", 80, "w")],
                                dots=True, on_open=lambda i: app.open_detail(i.split("#")[0]), height=6)
        self.recent.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        c4 = make_card(bot)
        c4.grid(row=0, column=1, sticky="nsew", padx=(7, 0))
        card_header(c4, "Jobs by Type")
        self.types = BarList(c4)
        self.types.pack(fill="x", padx=18)

    def refresh(self):
        db = self.app.db
        c = db.status_counts()
        total = sum(c.values())
        pct = lambda n: f"{n * 100 // total}% of all jobs" if total else " "
        self.k["total"].set(total, f"{db.count_txns(1)} archived not counted")
        self.k["completed"].set(c["Completed"], pct(c["Completed"]))
        self.k["ongoing"].set(c["Assigned"] + c["In Progress"], f"{c['Assigned']} assigned · {c['In Progress']} in progress")
        self.k["pending"].set(c["Pending"], f"{c['Rescheduled']} rescheduled · {c['Failed']} failed")
        self.k["cancelled"].set(c["Cancelled"], pct(c["Cancelled"]))
        self.bars.set([(s, c[s], STATUS_COLORS[s]) for s in STATUSES])
        self.types.set([(t, n, SLATE) for t, n in db.type_counts()[:8]])
        today, rows = date.today(), []
        for label, kind in (("Today", "Daily"), ("This Week", "Weekly"), ("This Month", "Monthly")):
            k = db.report(kind, today)["kpis"]
            rows.append((label, (label, k["Handled"], k["Created"], k["Completed"], k["Cancelled"], k["Updates"]), None))
        self.summary.load(rows)
        self.recent.load([
            (f"{h['txn_id']}#{h['id']}",
             (nice(h["event_at"]), h["txn_id"], h["event_type"], (h["description"] or "")[:70], h["updated_by"]),
             h["new_status"]) for h in db.history_search(limit=12)])


class TransactionsPage(Page):
    title = "Transactions"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Search, filter and manage every technician transaction"
        self.header(("Export CSV", self.export, "secondary"),
                    ("+  New Transaction", app.new_transaction, "primary"))
        self.v = {k: tk.StringVar() for k in ("q", "tech", "type", "status", "dfrom", "dto")}
        self.field = tk.StringVar(value="All")
        fc = make_card(self)
        fc.pack(fill="x", pady=(0, 12))
        inner = tk.Frame(fc, bg=WHITE, padx=16, pady=12)
        inner.pack(fill="x")
        for i, w in enumerate((0, 3, 2, 2, 2, 1, 1, 0)):
            inner.columnconfigure(i, weight=w)
        spec = [("Search in", 0), ("Search", 1), ("Technician", 2), ("Job Type", 3), ("Job Status", 4),
                ("From (YYYY-MM-DD)", 5), ("To (YYYY-MM-DD)", 6)]
        for text, c in spec:
            small_label(inner, text).grid(row=0, column=c, sticky="w", padx=(0 if c == 0 else 8, 0))
        pad = lambda c: (0 if c == 0 else 8, 0)
        ttk.Combobox(inner, textvariable=self.field, state="readonly", width=14,
                     values=["All", "Customer", "Account No.", "Technician", "Transaction ID"]).grid(
            row=1, column=0, sticky="ew")
        self.search = ttk.Entry(inner, textvariable=self.v["q"])
        self.search.grid(row=1, column=1, sticky="ew", padx=pad(1))
        self.cb_tech = ttk.Combobox(inner, textvariable=self.v["tech"], state="readonly")
        self.cb_tech.grid(row=1, column=2, sticky="ew", padx=pad(2))
        ttk.Combobox(inner, textvariable=self.v["type"], state="readonly",
                     values=["All Job Types"] + JOB_TYPES).grid(row=1, column=3, sticky="ew", padx=pad(3))
        ttk.Combobox(inner, textvariable=self.v["status"], state="readonly",
                     values=["All Statuses"] + STATUSES).grid(row=1, column=4, sticky="ew", padx=pad(4))
        ttk.Entry(inner, textvariable=self.v["dfrom"], width=12).grid(row=1, column=5, sticky="ew", padx=pad(5))
        ttk.Entry(inner, textvariable=self.v["dto"], width=12).grid(row=1, column=6, sticky="ew", padx=pad(6))
        Btn(inner, "Clear", self.clear).grid(row=1, column=7, padx=(8, 0))
        self.clear(refresh=False)
        for var in list(self.v.values()) + [self.field]:
            var.trace_add("write", self.schedule)

        tc = make_card(self)
        tc.pack(fill="both", expand=True)
        self.table = DataTable(tc, TXN_COLS, dots=True, on_open=app.open_detail)
        self.table.pack(fill="both", expand=True, padx=1, pady=(1, 0))
        foot = tk.Frame(tc, bg=WHITE, padx=14, pady=10)
        foot.pack(fill="x")
        self.count = tk.Label(foot, text="", font=(FONT, 9), bg=WHITE, fg=MUTED)
        self.count.pack(side="left")
        Btn(foot, "Archive", self.archive, "danger").pack(side="right")
        Btn(foot, "Update", self.update_sel).pack(side="right", padx=8)
        Btn(foot, "View Details", self.view).pack(side="right")

    def clear(self, refresh=True):
        self.v["q"].set("")
        self.v["tech"].set("All Technicians")
        self.v["type"].set("All Job Types")
        self.v["status"].set("All Statuses")
        self.v["dfrom"].set("")
        self.v["dto"].set("")
        self.field.set("All")
        if refresh:
            self.refresh()

    def _opt(self, key, allv):
        val = self.v[key].get()
        return "" if val == allv else val

    def rows(self):
        return self.app.db.search(
            self.v["q"].get().strip(), self.field.get(), self._opt("tech", "All Technicians"),
            self._opt("type", "All Job Types"), self._opt("status", "All Statuses"),
            valid_date(self.v["dfrom"].get()), valid_date(self.v["dto"].get()))

    def refresh(self):
        self.cb_tech["values"] = ["All Technicians", "(Unassigned)"] + self.app.db.technician_names(False)
        rows = self.rows()
        self.table.load([txn_row(r) for r in rows])
        self.count.configure(text=f"Showing {len(rows)} of {self.app.db.count_txns()} active transactions")

    def _sel(self):
        s = self.table.selected()
        if not s:
            messagebox.showinfo("Select a record", "Select a transaction in the table first.", parent=self.app.root)
        return s

    def view(self):
        s = self._sel()
        if s:
            self.app.open_detail(s)

    def update_sel(self):
        s = self._sel()
        if s:
            TxnForm(self.app, self.app.db.get_txn(s))

    def archive(self):
        s = self._sel()
        if s:
            self.app.archive(s, True)

    def export(self):
        self.app.export_csv("transactions.csv", [c[1] for c in TXN_COLS[:7]] + ["Completed", "Priority", "Concern",
                            "Action Taken", "Remarks"], [(r["txn_id"], r["created_at"], r["customer"], r["account_no"],
                            r["technician"], r["job_type"], r["status"], r["completed_at"] or "", r["priority"],
                            r["concern"], r["action_taken"], r["remarks"]) for r in self.rows()])


class TechniciansPage(Page):
    title = "Technicians"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Workload and progress for every technician"
        self.header(("Activate / Deactivate", self.toggle, "secondary"), ("Edit Phone", self.edit, "secondary"),
                    ("+  Add Technician", self.add, "primary"))
        self.rowconfigure(1, weight=1)
        self.rowconfigure(2, weight=1)
        self.columnconfigure(0, weight=1)
        self.pack_propagate(True)
        # header() packs; use a container for the two tables
        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1)
        body.rowconfigure(0, weight=1, uniform="t")
        body.rowconfigure(1, weight=1, uniform="t")
        c1 = make_card(body)
        c1.grid(row=0, column=0, sticky="nsew", pady=(0, 7))
        card_header(c1, "Technician Performance", "active jobs only · archived excluded")
        cols = [("n", "Technician", 150, "w"), ("p", "Phone", 105, "w"), ("s", "Status", 70, "w"),
                ("a", "Assigned", 72, "center"), ("st", "Started", 66, "center"), ("ip", "In Progress", 82, "center"),
                ("c", "Completed", 82, "center"), ("pe", "Pending", 68, "center"), ("f", "Failed", 60, "center"),
                ("r", "Rescheduled", 90, "center"), ("t", "Total", 56, "center")]
        self.table = DataTable(c1, cols, dots=True, height=5)
        self.table.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        self.table.tree.bind("<<TreeviewSelect>>", lambda e: self.load_jobs())
        c2 = make_card(body)
        c2.grid(row=1, column=0, sticky="nsew", pady=(7, 0))
        self.jobs_hdr = card_header(c2, "Assigned Jobs & Latest Remarks", "select a technician above")
        self.jobs = DataTable(c2, [("id", "Transaction", 112, "w"), ("c", "Customer", 140, "w"),
                                   ("t", "Job Type", 150, "w"), ("s", "Status", 90, "w"),
                                   ("u", "Last Update", 140, "w"), ("r", "Latest Remark", 300, "w")],
                              dots=True, on_open=app.open_detail, height=5)
        self.jobs.pack(fill="both", expand=True, padx=1, pady=(0, 1))

    def refresh(self):
        rows = []
        for name, phone, active, c in self.app.db.technician_stats():
            st = "Active" if active else "Inactive"
            rows.append((name or "__none__", (name or "Unassigned", phone, st, c["Assigned"], c["Started"],
                                              c["In Progress"], c["Completed"], c["Pending"], c["Failed"],
                                              c["Rescheduled"], c["Total"]), st))
        self.table.load(rows)
        self.load_jobs()

    def _name(self):
        s = self.table.selected()
        return None if s is None else ("" if s == "__none__" else s)

    def load_jobs(self):
        name = self._name()
        if name is None:
            self.jobs.load([])
            return
        self.jobs.load([(r["txn_id"], (r["txn_id"], r["customer"], r["job_type"], r["status"],
                                       nice(r["last_at"]), r["last_desc"] or ""), r["status"])
                        for r in self.app.db.tech_jobs(name)])

    def add(self):
        TechDialog(self.app)

    def edit(self):
        n = self._name()
        if not n:
            return messagebox.showinfo("Select a technician", "Select a technician first.", parent=self.app.root)
        TechDialog(self.app, n)

    def toggle(self):
        n = self._name()
        if not n:
            return messagebox.showinfo("Select a technician", "Select a technician first.", parent=self.app.root)
        r = self.app.db.conn.execute("SELECT active FROM tm_technicians WHERE name=?", (n,)).fetchone()
        self.app.db.update_technician(n, active=not r["active"])
        self.app.refresh_all()


class ReportsPage(Page):
    title = "Reports"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Technician workload, completed and pending jobs, and overall activity"
        self.header(("Export CSV", self.export, "secondary"))
        self.kind = tk.StringVar(value="Weekly")
        self.ref = tk.StringVar(value=date.today().strftime("%Y-%m-%d"))
        self.data = None
        ctl = make_card(self)
        ctl.pack(fill="x", pady=(0, 12))
        ci = tk.Frame(ctl, bg=WHITE, padx=16, pady=12)
        ci.pack(fill="x")
        small_label(ci, "Report").grid(row=0, column=0, sticky="w")
        ttk.Combobox(ci, textvariable=self.kind, state="readonly", width=12,
                     values=["Daily", "Weekly", "Monthly"]).grid(row=1, column=0)
        small_label(ci, "Reference date").grid(row=0, column=2, sticky="w", padx=(14, 0))
        Btn(ci, "◀", lambda: self.step(-1)).grid(row=1, column=1, padx=(8, 0))
        e = ttk.Entry(ci, textvariable=self.ref, width=12)
        e.grid(row=1, column=2, padx=(14, 0))
        e.bind("<Return>", lambda ev: self.refresh())
        Btn(ci, "▶", lambda: self.step(1)).grid(row=1, column=3, padx=(8, 0))
        Btn(ci, "Today", self.today).grid(row=1, column=4, padx=(8, 0))
        self.plabel = tk.Label(ci, text="", font=(FONT, 12, "bold"), bg=WHITE, fg=TEXT)
        self.plabel.grid(row=1, column=5, padx=(24, 0))
        self.kind.trace_add("write", self.schedule)

        kp = tk.Frame(self, bg=BG)
        kp.pack(fill="x", pady=(0, 12))
        self.k = {}
        defs = [("Handled", "Jobs Handled", SLATE), ("Created", "New Jobs", ACCENT), ("Completed", "Completed", GREEN),
                ("Ongoing", "Ongoing", INDIGO), ("Pending", "Pending", AMBER), ("Failed", "Failed", RED),
                ("Rescheduled", "Rescheduled", ORANGE), ("Cancelled", "Cancelled", "#94A3B8")]
        for i, (key, title, color) in enumerate(defs):
            kp.columnconfigure(i, weight=1, uniform="rk")
            self.k[key] = KpiCard(kp, title, color)
            self.k[key].grid(row=0, column=i, sticky="nsew", padx=(0 if i == 0 else 5, 0 if i == 7 else 5))
        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True)
        body.columnconfigure(0, weight=1)
        body.rowconfigure((0, 1), weight=1, uniform="rt")
        rc = lambda first: [("n", first, 190, "w"), ("h", "Handled", 80, "center"), ("c", "Completed", 90, "center"),
                            ("o", "Ongoing", 80, "center"), ("p", "Pending", 80, "center"),
                            ("r", "Rescheduled", 95, "center"), ("f", "Failed", 70, "center"),
                            ("x", "Cancelled", 85, "center"), ("u", "Updates", 75, "center")]
        c1 = make_card(body)
        c1.grid(row=0, column=0, sticky="nsew", pady=(0, 6))
        card_header(c1, "Technician Workload", "status as at end of period")
        self.t1 = DataTable(c1, rc("Technician"), height=4)
        self.t1.pack(fill="both", expand=True, padx=1, pady=(0, 1))
        c2 = make_card(body)
        c2.grid(row=1, column=0, sticky="nsew", pady=(6, 0))
        card_header(c2, "Activity by Job Type")
        self.t2 = DataTable(c2, rc("Job Type"), height=4)
        self.t2.pack(fill="both", expand=True, padx=1, pady=(0, 1))

    def _date(self):
        d = valid_date(self.ref.get())
        return datetime.strptime(d, "%Y-%m-%d").date() if d else None

    def step(self, direction):
        d = self._date() or date.today()
        self.ref.set(shift_ref(self.kind.get(), d, direction).strftime("%Y-%m-%d"))
        self.refresh()

    def today(self):
        self.ref.set(date.today().strftime("%Y-%m-%d"))
        self.refresh()

    def refresh(self):
        d = self._date()
        if d is None:
            self.plabel.configure(text="Enter the date as YYYY-MM-DD", fg=RED)
            return
        self.data = self.app.db.report(self.kind.get(), d)
        self.plabel.configure(text=self.data["label"], fg=TEXT)
        for key, card in self.k.items():
            card.set(self.data["kpis"][key])
        for tbl, rows in ((self.t1, self.data["by_tech"]), (self.t2, self.data["by_type"])):
            tbl.load([(f"r{i}", tuple(r), None) for i, r in enumerate(rows)])

    def export(self):
        if not self.data:
            return
        head = ["Name", "Handled", "Completed", "Ongoing", "Pending", "Rescheduled", "Failed", "Cancelled", "Updates"]
        rows = [[f"{self.kind.get()} report", self.data["label"]], [], ["TECHNICIAN WORKLOAD"], head] + \
               self.data["by_tech"] + [[], ["ACTIVITY BY JOB TYPE"], head] + self.data["by_type"]
        self.app.export_csv(f"{self.kind.get().lower()}_report.csv", None, rows)


class HistoryPage(Page):
    title = "History"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Complete audit trail of every transaction update"
        self.header(("Export CSV", self.export, "secondary"))
        self.v = {k: tk.StringVar() for k in ("q", "ev", "dfrom", "dto")}
        fc = make_card(self)
        fc.pack(fill="x", pady=(0, 12))
        inner = tk.Frame(fc, bg=WHITE, padx=16, pady=12)
        inner.pack(fill="x")
        inner.columnconfigure(0, weight=1)
        for c, t in enumerate(("Search (transaction, customer, account, remarks, user)", "Event", "From (YYYY-MM-DD)",
                               "To (YYYY-MM-DD)")):
            small_label(inner, t).grid(row=0, column=c, sticky="w", padx=(0 if c == 0 else 8, 0))
        ttk.Entry(inner, textvariable=self.v["q"]).grid(row=1, column=0, sticky="ew")
        ttk.Combobox(inner, textvariable=self.v["ev"], state="readonly", values=["All Events"] + EVENT_TYPES,
                     width=16).grid(row=1, column=1, padx=(8, 0))
        ttk.Entry(inner, textvariable=self.v["dfrom"], width=13).grid(row=1, column=2, padx=(8, 0))
        ttk.Entry(inner, textvariable=self.v["dto"], width=13).grid(row=1, column=3, padx=(8, 0))
        Btn(inner, "Clear", self.clear).grid(row=1, column=4, padx=(8, 0))
        self.v["ev"].set("All Events")
        for var in self.v.values():
            var.trace_add("write", self.schedule)
        tc = make_card(self)
        tc.pack(fill="both", expand=True)
        self.table = DataTable(tc, [("t", "Date & Time", 140, "w"), ("id", "Transaction", 112, "w"),
                                    ("c", "Customer", 120, "w"), ("e", "Event", 95, "w"), ("p", "Previous", 85, "w"),
                                    ("n", "New", 85, "w"), ("b", "Updated By", 90, "w"),
                                    ("d", "Description", 260, "w")], dots=True,
                               on_open=lambda i: app.open_detail(i.split("#")[0]))
        self.table.pack(fill="both", expand=True, padx=1, pady=1)
        self.count = tk.Label(tc, text="", font=(FONT, 9), bg=WHITE, fg=MUTED, anchor="w")
        self.count.pack(fill="x", padx=14, pady=8)

    def clear(self):
        for k in ("q", "dfrom", "dto"):
            self.v[k].set("")
        self.v["ev"].set("All Events")

    def rows(self):
        ev = self.v["ev"].get()
        return self.app.db.history_search(self.v["q"].get().strip(), "" if ev == "All Events" else ev,
                                          valid_date(self.v["dfrom"].get()), valid_date(self.v["dto"].get()))

    def refresh(self):
        rows = self.rows()
        self.table.load([(f"{h['txn_id']}#{h['id']}",
                          (nice(h["event_at"]), h["txn_id"], h["customer"] or "", h["event_type"],
                           h["prev_status"] or "—", h["new_status"] or "—", h["updated_by"],
                           h["description"] or ""), h["new_status"]) for h in rows])
        self.count.configure(text=f"{len(rows)} events shown (newest first, up to 2,000)")

    def export(self):
        self.app.export_csv("history.csv", ["Date & Time", "Transaction ID", "Customer", "Account No.", "Technician",
                            "Event", "Previous Status", "New Status", "Updated By", "Description", "Changes"],
                            [(h["event_at"], h["txn_id"], h["customer"], h["account_no"], h["technician"],
                              h["event_type"], h["prev_status"] or "", h["new_status"] or "", h["updated_by"],
                              h["description"], h["changes"]) for h in self.rows()])


class ArchivePage(Page):
    title = "Archive"

    def __init__(self, parent, app):
        super().__init__(parent, app)
        self.subtitle = "Archived transactions are hidden from active lists but keep their full history"
        self.q = tk.StringVar()
        fc = make_card(self)
        fc.pack(fill="x", pady=(0, 12))
        inner = tk.Frame(fc, bg=WHITE, padx=16, pady=12)
        inner.pack(fill="x")
        inner.columnconfigure(0, weight=1)
        small_label(inner, "Search archived transactions").grid(row=0, column=0, sticky="w")
        ttk.Entry(inner, textvariable=self.q).grid(row=1, column=0, sticky="ew")
        self.q.trace_add("write", self.schedule)
        tc = make_card(self)
        tc.pack(fill="both", expand=True)
        self.table = DataTable(tc, TXN_COLS, dots=True, on_open=app.open_detail)
        self.table.pack(fill="both", expand=True, padx=1, pady=(1, 0))
        foot = tk.Frame(tc, bg=WHITE, padx=14, pady=10)
        foot.pack(fill="x")
        Btn(foot, "Restore", self.restore, "primary").pack(side="right")
        Btn(foot, "View Details", self.view).pack(side="right", padx=8)

    def refresh(self):
        self.table.load([txn_row(r) for r in self.app.db.search(self.q.get().strip(), archived=1)])

    def view(self):
        s = self.table.selected()
        if s:
            self.app.open_detail(s)

    def restore(self):
        s = self.table.selected()
        if s:
            self.app.archive(s, False)


# ------------------------------------------------------------------ shell
class NavItem(tk.Frame):
    def __init__(self, parent, icon, text, command):
        super().__init__(parent, bg=NAVY, cursor="hand2")
        self.active = False
        self.bar = tk.Frame(self, bg=NAVY, width=3)
        self.bar.pack(side="left", fill="y")
        self.icon = tk.Label(self, text=icon, font=(SYMBOL, 13), fg="#9FB3C8", bg=NAVY, width=4)
        self.icon.pack(side="left", pady=11)
        self.text = tk.Label(self, text=text, font=(FONT, 10), fg="#C7D2E0", bg=NAVY, anchor="w")
        self.text.pack(side="left", fill="x", expand=True)
        for w in (self, self.icon, self.text):
            w.bind("<Enter>", lambda e: self._paint(True))
            w.bind("<Leave>", lambda e: self._paint(False))
            w.bind("<Button-1>", lambda e: command())

    def _paint(self, hover):
        bg = SLATE if self.active else ("#1C3350" if hover else NAVY)
        for w in (self, self.icon, self.text):
            w.configure(bg=bg)
        self.bar.configure(bg=ACCENT if self.active else bg)
        self.icon.configure(fg=WHITE if self.active else "#9FB3C8")
        self.text.configure(fg=WHITE if self.active else "#C7D2E0",
                            font=(FONT, 10, "bold" if self.active else "normal"))

    def set_active(self, on):
        self.active = on
        self._paint(False)

    def collapse(self, flag):
        if flag:
            self.text.pack_forget()
        else:
            self.text.pack(side="left", fill="x", expand=True)


class App:
    NAV = [("dashboard", "Dashboard", "▦", DashboardPage), ("transactions", "Transactions", "☰", TransactionsPage),
           ("technicians", "Technicians", "☺", TechniciansPage), ("reports", "Reports", "▤", ReportsPage),
           ("history", "History", "◷", HistoryPage), ("archive", "Archive", "▭", ArchivePage)]

    def __init__(self, db):
        self.db = db
        self.detail_windows = set()
        self.collapsed = self.manual = self.auto = False
        self.current = None
        try:
            from ctypes import windll
            windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
        self.root = tk.Tk()
        self.root.title("Imperial Network · TechTrack")
        self.root.geometry("1380x820")
        self.root.minsize(980, 640)
        self.root.configure(bg=BG)
        setup_style(self.root)
        self.user = db.get_setting("operator", "")
        self.build_shell()
        self.show("dashboard")
        self.root.bind("<Control-n>", lambda e: self.new_transaction())
        self.root.bind("<Configure>", self.on_resize)
        self.tick()
        if not self.user:
            self.user = "Admin"
            self.root.after(400, self.change_user)

    # ---- layout
    def build_shell(self):
        r = self.root
        r.columnconfigure(1, weight=1)
        r.rowconfigure(0, weight=1)
        self.sidebar = tk.Frame(r, bg=NAVY, width=236)
        self.sidebar.grid(row=0, column=0, sticky="ns")
        self.sidebar.pack_propagate(False)
        self.brand = tk.Frame(self.sidebar, bg=NAVY, height=72)
        self.brand.pack(fill="x")
        self.brand.pack_propagate(False)
        tk.Label(self.brand, text="◆", font=(SYMBOL, 18), fg=ACCENT, bg=NAVY).pack(side="left", padx=(22, 10))
        self.brand_text = tk.Frame(self.brand, bg=NAVY)
        self.brand_text.pack(side="left")
        tk.Label(self.brand_text, text="Imperial Network", font=(FONT, 11, "bold"), fg=WHITE, bg=NAVY).pack(anchor="w")
        tk.Label(self.brand_text, text="TechTrack", font=(FONT, 9), fg="#8FA3BA", bg=NAVY).pack(anchor="w")
        tk.Frame(self.sidebar, bg="#22364F", height=1).pack(fill="x", padx=16, pady=(0, 10))
        self.nav = {}
        for key, label, icon, _ in self.NAV:
            item = NavItem(self.sidebar, icon, label, lambda k=key: self.show(k))
            item.pack(fill="x", pady=1)
            self.nav[key] = item
        self.footer = tk.Label(self.sidebar, text="Technician Monitoring v4", font=(FONT, 8), fg="#6F849C", bg=NAVY)
        self.footer.pack(side="bottom", pady=14)

        main = tk.Frame(r, bg=BG)
        main.grid(row=0, column=1, sticky="nsew")
        main.columnconfigure(0, weight=1)
        main.rowconfigure(1, weight=1)
        top = tk.Frame(main, bg=WHITE, height=62)
        top.grid(row=0, column=0, sticky="ew")
        top.pack_propagate(False)
        tk.Frame(top, bg=BORDER, height=1).pack(side="bottom", fill="x")
        burger = tk.Label(top, text="☰", font=(SYMBOL, 15), fg=MUTED, bg=WHITE, cursor="hand2", padx=18)
        burger.pack(side="left")
        burger.bind("<Button-1>", lambda e: self.toggle_sidebar())
        self.title_lbl = tk.Label(top, text="", font=(FONT, 15, "bold"), fg=TEXT, bg=WHITE)
        self.title_lbl.pack(side="left")
        Btn(top, "+  New Transaction", self.new_transaction, "primary").pack(side="right", padx=(10, 20), pady=11)
        self.user_lbl = tk.Label(top, text="", font=(FONT, 10), fg=TEXT, bg=HOVER, padx=12, pady=6,
                                 cursor="hand2", highlightthickness=1, highlightbackground=BORDER)
        self.user_lbl.pack(side="right", pady=14)
        self.user_lbl.bind("<Button-1>", lambda e: self.change_user())
        self.clock = tk.Label(top, text="", font=(FONT, 10), fg=MUTED, bg=WHITE)
        self.clock.pack(side="right", padx=18)
        self.update_user_label()

        content = tk.Frame(main, bg=BG)
        content.grid(row=1, column=0, sticky="nsew")
        content.columnconfigure(0, weight=1)
        content.rowconfigure(0, weight=1)
        self.pages = {}
        for key, _, _, cls in self.NAV:
            p = cls(content, self)
            p.grid(row=0, column=0, sticky="nsew", padx=26, pady=(20, 22))
            self.pages[key] = p

    def show(self, key):
        self.current = key
        self.pages[key].tkraise()
        self.pages[key].refresh()
        self.title_lbl.configure(text=self.pages[key].title)
        for k, item in self.nav.items():
            item.set_active(k == key)

    def set_collapsed(self, flag):
        self.collapsed = flag
        self.sidebar.configure(width=68 if flag else 236)
        for item in self.nav.values():
            item.collapse(flag)
        if flag:
            self.brand_text.pack_forget()
            self.footer.pack_forget()
        else:
            self.brand_text.pack(side="left")
            self.footer.pack(side="bottom", pady=14)

    def toggle_sidebar(self):
        self.manual, self.auto = True, False
        self.set_collapsed(not self.collapsed)

    def on_resize(self, e):
        if e.widget is not self.root or self.manual:
            return
        narrow = e.width < 1240
        if narrow and not self.collapsed:
            self.set_collapsed(True)
            self.auto = True
        elif not narrow and self.collapsed and self.auto:
            self.set_collapsed(False)
            self.auto = False

    def tick(self):
        self.clock.configure(text=datetime.now().strftime("%a, %b %d  ·  %I:%M %p"))
        self.root.after(30000, self.tick)

    def update_user_label(self):
        self.user_lbl.configure(text=f"●  {self.user or 'Admin'}")

    def change_user(self):
        name = simpledialog.askstring("Current user", "Your name (saved with every update you make):",
                                      initialvalue=self.user or "Admin", parent=self.root)
        if name and name.strip():
            self.user = name.strip()
        self.user = self.user or "Admin"
        self.db.set_setting("operator", self.user)
        self.update_user_label()

    # ---- actions shared by pages
    def refresh_all(self):
        for p in self.pages.values():
            p.refresh()
        for w in list(self.detail_windows):
            try:
                w.render()
            except tk.TclError:
                self.detail_windows.discard(w)

    def new_transaction(self):
        TxnForm(self, None, on_saved=lambda tid: self.open_detail(tid))

    def open_detail(self, tid):
        for w in self.detail_windows:
            if w.tid == tid:
                w.lift()
                return
        TxnDetail(self, tid)

    def archive(self, tid, flag, parent=None):
        parent = parent or self.root
        if flag and not messagebox.askyesno(
                "Archive transaction",
                f"Archive {tid}?\n\nIt will be hidden from active lists, but its complete history is kept. "
                "You can restore it any time from the Archive page.", parent=parent):
            return False
        self.db.set_archived(tid, flag, self.user)
        self.refresh_all()
        return True

    def export_csv(self, default, headers, rows):
        path = filedialog.asksaveasfilename(parent=self.root, defaultextension=".csv", initialfile=default,
                                            filetypes=[("CSV file", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                if headers:
                    w.writerow(headers)
                w.writerows(rows)
        except OSError as e:
            return messagebox.showerror("Export failed", str(e), parent=self.root)
        messagebox.showinfo("Export complete", f"Saved {len(rows)} rows to\n{path}", parent=self.root)

    def run(self):
        self.root.mainloop()


# ------------------------------------------------------------------ demo data
def seed_demo(db):
    if db.count_txns(0) or db.count_txns(1):
        print("Database already has transactions - demo data skipped.")
        return
    rnd = random.Random(7)
    for n, p in (("Marco Dela Cruz", "0917 555 0101"), ("Janelle Reyes", "0918 555 0144"),
                 ("Paolo Santos", "0920 555 0178"), ("Ana Villanueva", "0919 555 0123")):
        db.add_technician(n, p)
    techs = db.technician_names()
    customers = ["Lorna Bautista", "Ramon Aquino", "Elena Cruz", "Jose Mercado", "Carla Domingo", "Rey Navarro",
                 "Maricel Ramos", "Dennis Flores", "Grace Tolentino", "Arnel Castillo", "Joy Pascual", "Noel Garcia"]
    concerns = {
        "Installation": "New fiber connection - Plan 50 Mbps", "Repair / Troubleshooting": "No internet, red LOS light",
        "Reconfiguration": "Change PPPoE credentials and VLAN", "ONU / Router Replacement": "Router overheating, replace unit",
        "Wi-Fi Configuration": "Weak Wi-Fi signal in 2nd floor", "Site Visit": "Pre-installation site survey",
        "Customer Complaint": "Repeated disconnections reported", "Other Technical Activity": "Cable re-route request"}
    now = datetime.now()
    created = []
    for i in range(52):
        when = min(now - timedelta(days=rnd.randint(0, 40), hours=rnd.randint(0, 9), minutes=rnd.randint(0, 59)), now)
        jt = rnd.choice(JOB_TYPES)
        tech = rnd.choice(techs) if rnd.random() > .15 else ""
        d = {"customer": rnd.choice(customers), "account_no": f"IN-{rnd.randint(10000, 99999)}", "technician": tech,
             "job_type": jt, "priority": rnd.choice(PRIORITIES), "concern": concerns[jt],
             "status": "Assigned" if tech else "Pending"}
        tid = db.create_txn(d, "Dispatcher", when=when)
        t = when
        if tech and rnd.random() < .85:
            t = min(t + timedelta(hours=rnd.randint(1, 5)), now)
            db.update_txn(tid, {"status": "In Progress", "action_taken": "Arrived on site, checking line."},
                          tech, "Technician on site", when=t)
            r = rnd.random()
            t = min(t + timedelta(hours=rnd.randint(1, 4)), now)
            if r < .68:
                db.update_txn(tid, {"status": "Completed", "action_taken": "Resolved and tested connection.",
                                    "remarks": "Customer confirmed service is working."}, tech,
                              "Job finished, customer signed off", when=t)
                created.append((tid, t))
            elif r < .78:
                db.update_txn(tid, {"status": "Failed"}, tech, "Customer not home during visit", when=t)
            elif r < .88:
                db.update_txn(tid, {"status": "Rescheduled"}, tech, "Customer requested another day", when=t)
            elif r < .93:
                db.update_txn(tid, {"status": "Cancelled"}, "Dispatcher", "Customer cancelled the request", when=t)
    for tid, t in created[:3]:
        if now - t > timedelta(days=20):
            db.set_archived(tid, True, "Admin", when=t + timedelta(days=1))
    print("Demo data created.")


def main():
    ap = argparse.ArgumentParser(description="Imperial Network TechTrack - Technician Monitoring System")
    ap.add_argument("--db", default=str(DEFAULT_DB), help="database file (default: techtrack.db beside this script)")
    ap.add_argument("--demo", action="store_true", help="add sample data when the monitoring tables are empty")
    args = ap.parse_args()
    db = Database(args.db)
    if args.demo:
        seed_demo(db)
    App(db).run()


if __name__ == "__main__":
    main()
