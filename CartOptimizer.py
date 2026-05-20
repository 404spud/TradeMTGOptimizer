import argparse
import json
import os
import re
import sys
import sqlite3
from typing import Dict, List, Tuple, Optional, Set
from datetime import datetime
from decimal import Decimal, ROUND_HALF_UP
import unicodedata
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup
from bs4.element import Tag, NavigableString
import pandas as pd
from pulp import (
    LpProblem, LpMinimize, LpVariable, lpSum,
    LpBinary, LpInteger, PULP_CBC_CMD
)

# ----------------------------
# Console helpers
# ----------------------------

def print_colored(text: str, color_code: str) -> None:
    COLORS = {
        "red": "\033[38;5;209m",
        "green": "\033[38;5;32m",
        "yellow": "\033[38;5;229m",
        "blue": "\033[38;5;153m",
        "reset": "\033[38;5;255m"
    }
    print(f"{COLORS.get(color_code, COLORS['reset'])}{text}{COLORS['reset']}")

def safe_var_name(s: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", s).strip("_")
    return out[:80] if out else "seller"

def get_local_date_brisbane() -> str:
    try:
        from zoneinfo import ZoneInfo
        return datetime.now(ZoneInfo("Australia/Brisbane")).strftime("%Y-%m-%d")
    except Exception:
        return datetime.now().strftime("%Y-%m-%d")

def money_to_cents_from_input(s: str) -> int:
    d = Decimal(s.strip())
    cents = int((d * 100).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
    return cents

def money_to_cents_from_site(price_text: str) -> Optional[int]:
    cleaned = re.sub(r"[^\d.]", "", price_text or "")
    if cleaned == "":
        return None
    try:
        d = Decimal(cleaned)
        cents = int((d * 100).quantize(Decimal("1"), rounding=ROUND_HALF_UP))
        return cents
    except Exception:
        return None

def fmt_aud(cents: Optional[int]) -> str:
    if cents is None:
        return "n/a"
    sign = "-" if cents < 0 else ""
    cents_abs = abs(int(cents))
    dollars = cents_abs // 100
    rem = cents_abs % 100
    return f"{sign}${dollars}.{rem:02d}"

def norm_name(s: str) -> str:
    s = s.strip().casefold()
    s = unicodedata.normalize("NFKD", s)
    s = "".join(ch for ch in s if not unicodedata.combining(ch))
    s = " ".join(s.split())
    return s

# ----------------------------
# Config and constants
# ----------------------------

DEFAULT_CONFIG_PATH = "config.json"
DEFAULT_LISTS_INDEX_PATH = "lists_index.json"
DEFAULT_LIST_FOLDER = "lists"
DEFAULT_OUTPUT_FOLDER = "outputs"
DEFAULT_DATA_FOLDER = "data"
DEFAULT_TRACKING_DB = os.path.join(DEFAULT_DATA_FOLDER, "tracking.sqlite")
DEFAULT_SHIPPING_FILE = "shipping_costs.json"

QUALIFIED_FILL_NUM = 95   # 0.95
QUALIFIED_FILL_DEN = 100
NEAR_LOW_THRESHOLD_CENTS = 660  # 6.60
DELTA_NOISE_BAND_CENTS = 100    # 1.00

ALLOWED_SOURCES = {"trademagic", "mtgmate"}
DEFAULT_SOURCES = ["trademagic", "mtgmate"]

# ----------------------------
# JSON helpers
# ----------------------------

def load_json(path: str, default):
    if not os.path.exists(path):
        return default
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def save_json(path: str, data) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=False)

def load_config(config_path: str = DEFAULT_CONFIG_PATH) -> dict:
    if not os.path.exists(config_path):
        cfg = {
            "version": 1,
            "default_list_folder": DEFAULT_LIST_FOLDER,
            "default_output_folder": DEFAULT_OUTPUT_FOLDER,
            "lists_index_path": DEFAULT_LISTS_INDEX_PATH,
            "tracking_db_path": DEFAULT_TRACKING_DB
        }
        save_json(config_path, cfg)
        print_colored(f"Created default config at {config_path}", "yellow")
        return cfg

    cfg = load_json(config_path, {})
    cfg.setdefault("version", 1)
    cfg.setdefault("default_list_folder", DEFAULT_LIST_FOLDER)
    cfg.setdefault("default_output_folder", DEFAULT_OUTPUT_FOLDER)
    cfg.setdefault("lists_index_path", DEFAULT_LISTS_INDEX_PATH)
    cfg.setdefault("tracking_db_path", DEFAULT_TRACKING_DB)
    return cfg

def load_lists_index(index_path: str) -> dict:
    if not os.path.exists(index_path):
        idx = {"version": 1, "lists": []}
        save_json(index_path, idx)
        return idx
    idx = load_json(index_path, {"version": 1, "lists": []})
    idx.setdefault("version", 1)
    idx.setdefault("lists", [])
    return idx

def find_list_entry(index: dict, list_id: str) -> Optional[dict]:
    for entry in index.get("lists", []):
        if str(entry.get("id")) == str(list_id):
            return entry
    return None

def next_numeric_id(index: dict) -> str:
    max_id = 0
    for entry in index.get("lists", []):
        try:
            n = int(str(entry.get("id")))
            if n > max_id:
                max_id = n
        except Exception:
            continue
    return str(max_id + 1)

def parse_sources_arg(s: str) -> List[str]:
    raw = (s or "").strip()
    if raw == "":
        return DEFAULT_SOURCES[:]
    parts = [p.strip().lower() for p in raw.split(",") if p.strip()]
    if not parts:
        return DEFAULT_SOURCES[:]
    bad = [p for p in parts if p not in ALLOWED_SOURCES]
    if bad:
        raise ValueError(f"Invalid sources: {', '.join(bad)}. Allowed: trademagic, mtgmate")
    # preserve order, de-dupe
    out = []
    seen = set()
    for p in parts:
        if p not in seen:
            out.append(p)
            seen.add(p)
    return out

# ----------------------------
# Card list parsing
# ----------------------------

QTY_NAME_PATTERN = re.compile(r"^(\d+)\s+(.+)$")

def parse_card_lines(lines: List[str]) -> Dict[str, int]:
    qty_map: Dict[str, int] = {}
    for raw in lines:
        line = raw.strip()
        if not line:
            continue

        m = QTY_NAME_PATTERN.match(line)
        if m:
            qty = int(m.group(1))
            name = m.group(2).strip()
        else:
            qty = 1
            name = line

        if not name:
            continue

        qty_map[name] = qty_map.get(name, 0) + qty

    return qty_map

def prompt_for_card_list() -> Dict[str, int]:
    print_colored(
        'Enter your card list. Formats: "2 Lightning Bolt" or "Lightning Bolt" (assumes 1). '
        "One per line. Blank line to finish:",
        "blue"
    )
    lines: List[str] = []
    while True:
        try:
            line = input()
        except EOFError:
            break
        if line.strip() == "":
            break
        lines.append(line)
    return parse_card_lines(lines)

def read_list_file(list_path: str) -> Dict[str, int]:
    if not os.path.exists(list_path):
        raise FileNotFoundError(f"List file not found: {list_path}")
    with open(list_path, "r", encoding="utf-8") as f:
        lines = [ln.rstrip("\n") for ln in f.readlines()]
    return parse_card_lines(lines)

def write_list_file(list_path: str, qty_map: Dict[str, int]) -> Tuple[int, int]:
    os.makedirs(os.path.dirname(list_path), exist_ok=True)
    unique_cards = len(qty_map)
    total_qty = sum(qty_map.values())

    with open(list_path, "w", encoding="utf-8") as f:
        for name, qty in qty_map.items():
            f.write(f"{qty} {name}\n")

    return unique_cards, total_qty

# ----------------------------
# TradeMagic scraping
# ----------------------------

def fetch_listings_trademagic(card_names: List[str]) -> pd.DataFrame:
    url = "https://trademagic.com.au/bulksearch.php"
    payload = {"multilineData": "\n".join(card_names)}

    session = requests.Session()
    session.headers.update({"User-Agent": "TradeMagicCartOptimizer/4.0 (personal use)"})

    resp = session.post(url, data=payload, timeout=30)
    if resp.status_code != 200:
        raise RuntimeError(f"TradeMagic fetch failed. Status code: {resp.status_code}")

    soup = BeautifulSoup(resp.content, "html.parser")
    table = soup.find("table", {"id": "myTable"})
    if table is None:
        raise RuntimeError("TradeMagic results table not found. Check card names.")

    rows = table.find_all("tr")
    listings: List[dict] = []

    for row in rows[1:]:
        cols = row.find_all("td")
        if len(cols) < 9:
            continue
        try:
            card_name = cols[0].text.strip()
            seller = cols[1].text.strip()
            set_name = cols[4].find("img")["title"].strip() if cols[4].find("img") else cols[4].text.strip()
            condition = cols[5].find("i")["title"].strip() if cols[5].find("i") else cols[5].text.strip()
            language = cols[6].text.strip()
            quantity = int(cols[7].text.strip())
            price_text = cols[8].text.strip()

            price_cents = money_to_cents_from_site(price_text)
            if price_cents is None:
                continue

            listings.append({
                "card_name": card_name,
                "seller": seller,
                "set": set_name,
                "condition": condition,
                "finish": "",                 # TradeMagic finish not yet parsed
                "language": language,
                "quantity": int(quantity),
                "price_cents": int(price_cents),
                "price": float(Decimal(price_cents) / Decimal(100)),
                "url": "",
                "source_card_name": card_name,
                "source": "trademagic",
            })
        except Exception:
            continue

    return pd.DataFrame(listings)

# ----------------------------
# MTGMATE scraping (decklist_results)
# ----------------------------

MTGMATE_BASE_URL = "https://www.mtgmate.com.au"
MTGMATE_PRINTING_HREF_RE = re.compile(r"^/cards/[^/]+/[^/]+/[^/?#]+")
MTGMATE_FINISH_RE = re.compile(r"\b(Nonfoil|Foil|Etched|Surge Foil)\b", re.IGNORECASE)
MTGMATE_AVAIL_RE = re.compile(r"Available\s*:\s*(\d+)", re.IGNORECASE)
MTGMATE_PRICE_RE = re.compile(r"\$([0-9]+(?:\.[0-9]+)?)")

def build_mtgmate_decklist_text(card_quantity_map: Dict[str, int]) -> str:
    # Use CRLF in decklist param
    return "\r\n".join([f"{qty} {name}" for name, qty in card_quantity_map.items()])

def fetch_mtgmate_decklist_results_html(decklist_text: str, timeout: int = 30) -> str:
    url = f"{MTGMATE_BASE_URL}/cards/decklist_results"
    params = {"utf8": "✓", "decklist": decklist_text, "commit": "Build Deck"}

    s = requests.Session()
    s.headers.update({"User-Agent": "TradeMagicCartOptimizer/4.0 (personal use)"})

    r = s.get(url, params=params, timeout=timeout)
    r.raise_for_status()
    return r.text

def mtgmate_match_heading_to_requested(
    heading: str,
    requested_names: List[str],
    requested_norm_to_name: Dict[str, str]
) -> Optional[str]:
    heading = heading.strip()
    if heading in requested_names:
        return heading

    # DFC expansion on MTGMATE side: "A // B"
    if " // " in heading:
        left = heading.split(" // ", 1)[0].strip()
        if left in requested_names:
            return left

    hn = norm_name(heading)
    if " // " in hn:
        hn_left = hn.split(" // ", 1)[0].strip()
        if hn_left in requested_norm_to_name:
            return requested_norm_to_name[hn_left]

    if hn in requested_norm_to_name:
        return requested_norm_to_name[hn]

    return None

def mtgmate_find_heading_markers(soup: BeautifulSoup, requested_names: List[str]) -> List[Tuple[Tag, str, str]]:
    requested_norm_to_name = {norm_name(n): n for n in requested_names}
    candidates: List[Tuple[Tag, str, str]] = []
    seen = set()

    for node in soup.find_all(string=True):
        if not isinstance(node, NavigableString):
            continue
        t = node.strip()
        if not t:
            continue

        matched = mtgmate_match_heading_to_requested(t, requested_names, requested_norm_to_name)
        if matched is None:
            continue

        parent = node.parent
        if not isinstance(parent, Tag):
            continue
        # Avoid anchors and list items (missing/insufficient sections)
        if parent.name in ("a", "li"):
            continue

        k = id(parent)
        if k in seen:
            continue
        seen.add(k)
        candidates.append((parent, matched, t))

    # Keep only markers that actually have a printing link after them
    markers: List[Tuple[Tag, str, str]] = []
    for parent, matched, heading_text in candidates:
        has_offer = False
        for el in parent.next_elements:
            if isinstance(el, Tag) and el.name == "a":
                href = el.get("href", "")
                if isinstance(href, str) and MTGMATE_PRINTING_HREF_RE.match(href):
                    has_offer = True
                    break
        if has_offer:
            markers.append((parent, matched, heading_text))

    return markers

def mtgmate_get_offer_context_text(anchor: Tag) -> str:
    node: Tag = anchor
    for _ in range(10):
        if not isinstance(node, Tag):
            break
        ctx = node.get_text(" ", strip=True)
        # We want a container that includes the set name plus "Available" plus "$"
        if "$" in ctx and "Available" in ctx:
            return ctx
        node = node.parent
    # fallback to nearest parent
    p = anchor.find_parent(True)
    return p.get_text(" ", strip=True) if isinstance(p, Tag) else anchor.get_text(" ", strip=True)

def mtgmate_parse_offer_line(anchor: Tag) -> Tuple[str, int, int]:
    ctx = mtgmate_get_offer_context_text(anchor)

    # finish
    finish = "Nonfoil"
    m = MTGMATE_FINISH_RE.search(ctx)
    if m:
        finish = m.group(1).title()

    # available
    m = MTGMATE_AVAIL_RE.search(ctx)
    if not m:
        raise ValueError("Could not parse available quantity")
    available = int(m.group(1))

    # price
    m = MTGMATE_PRICE_RE.search(ctx)
    if not m:
        raise ValueError("Could not parse price")
    price_cents = money_to_cents_from_input(m.group(1))

    return finish, available, price_cents

def fetch_listings_mtgmate(card_quantity_map: Dict[str, int]) -> pd.DataFrame:
    requested_names = list(card_quantity_map.keys())
    if not requested_names:
        return pd.DataFrame([])

    decklist_text = build_mtgmate_decklist_text(card_quantity_map)
    html = fetch_mtgmate_decklist_results_html(decklist_text)
    soup = BeautifulSoup(html, "html.parser")

    markers = mtgmate_find_heading_markers(soup, requested_names)
    marker_ids = set(id(m[0]) for m in markers)

    rows: List[dict] = []
    seen_hrefs: Set[str] = set()

    for marker_tag, requested_name, source_heading in markers:
        for el in marker_tag.next_elements:
            if isinstance(el, Tag):
                # stop when we reach another marker tag
                if id(el) in marker_ids and el is not marker_tag:
                    break
                if el.name != "a":
                    continue

                href = el.get("href", "")
                if not isinstance(href, str):
                    continue
                if not MTGMATE_PRINTING_HREF_RE.match(href):
                    continue
                # exclude decklist tool pages
                if href.startswith("/cards/decklist_"):
                    continue

                full_url = urljoin(MTGMATE_BASE_URL, href)
                if full_url in seen_hrefs:
                    continue
                seen_hrefs.add(full_url)

                set_name = el.get_text(" ", strip=True)

                try:
                    finish, available, price_cents = mtgmate_parse_offer_line(el)
                except Exception:
                    continue

                rows.append({
                    "card_name": requested_name,           # constraint key
                    "seller": "MTGMATE",
                    "set": set_name,
                    "condition": "Near Mint",              # per your instruction
                    "finish": finish,
                    "language": "English",
                    "quantity": int(available),
                    "price_cents": int(price_cents),
                    "price": float(Decimal(price_cents) / Decimal(100)),
                    "url": full_url,
                    "source_card_name": source_heading,    # MTGMATE heading text
                    "source": "mtgmate",
                })

    return pd.DataFrame(rows)

# ----------------------------
# Shipping costs (stored as cents in json)
# ----------------------------

def load_shipping_costs_cents(shipping_file: str) -> dict:
    raw = load_json(shipping_file, {}) if os.path.exists(shipping_file) else {}
    out: Dict[str, int] = {}

    for seller, val in raw.items():
        try:
            if isinstance(val, bool):
                continue
            if isinstance(val, int):
                if val >= 50:
                    out[seller] = int(val)
                else:
                    out[seller] = int(val) * 100
            elif isinstance(val, float):
                out[seller] = money_to_cents_from_input(str(val))
            elif isinstance(val, str):
                v = val.strip()
                if "." in v:
                    out[seller] = money_to_cents_from_input(v)
                else:
                    n = int(v)
                    out[seller] = n if n >= 50 else n * 100
        except Exception:
            continue

    return out

def save_shipping_costs_cents(shipping_file: str, shipping_costs_cents: dict) -> None:
    save_json(shipping_file, {k: int(v) for k, v in shipping_costs_cents.items()})

def get_shipping_cost_for_seller_cents(seller: str, shipping_costs_cents: dict) -> int:
    if seller in shipping_costs_cents:
        try:
            return int(shipping_costs_cents[seller])
        except Exception:
            pass

    print_colored(f"Enter the shipping cost for seller '{seller}' (in AUD): ", "blue")
    while True:
        raw = input(f"Shipping cost for seller '{seller}': ").strip()
        try:
            cents = money_to_cents_from_input(raw)
            shipping_costs_cents[seller] = int(cents)
            return int(cents)
        except Exception:
            print_colored("Invalid input. Please enter a numeric amount like 3.30", "red")

# ----------------------------
# Optimizer core (multi-source)
# ----------------------------

class OptimizeResult:
    def __init__(
        self,
        df_cart: pd.DataFrame,
        sellers_used: set,
        total_card_price_cents: int,
        total_shipping_cents: int,
        final_total_cents: int,
        missing_cards: List[str],
        requested_count: int,
        found_count: int,
        per_card_min_price_cents_by_source: Dict[str, Dict[str, Optional[int]]]
    ):
        self.df_cart = df_cart
        self.sellers_used = sellers_used
        self.total_card_price_cents = total_card_price_cents
        self.total_shipping_cents = total_shipping_cents
        self.final_total_cents = final_total_cents
        self.missing_cards = missing_cards
        self.requested_count = requested_count
        self.found_count = found_count
        self.per_card_min_price_cents_by_source = per_card_min_price_cents_by_source

def optimize_internal(
    card_quantity_map: Dict[str, int],
    sources: List[str],
    shipping_file: str = DEFAULT_SHIPPING_FILE
) -> OptimizeResult:
    if not card_quantity_map:
        raise ValueError("No cards provided.")

    requested_cards = list(card_quantity_map.keys())
    requested_count = len(requested_cards)

    df_parts: List[pd.DataFrame] = []
    per_source_min: Dict[str, Dict[str, Optional[int]]] = {src: {} for src in sources}

    # Fetch listings per source
    if "trademagic" in sources:
        df_tm = fetch_listings_trademagic(requested_cards)
        df_parts.append(df_tm)

        for c in requested_cards:
            sub = df_tm[df_tm["card_name"] == c] if not df_tm.empty else pd.DataFrame([])
            per_source_min["trademagic"][c] = None if sub.empty else int(sub["price_cents"].min())

    if "mtgmate" in sources:
        df_mm = fetch_listings_mtgmate(card_quantity_map)
        df_parts.append(df_mm)

        for c in requested_cards:
            sub = df_mm[df_mm["card_name"] == c] if not df_mm.empty else pd.DataFrame([])
            per_source_min["mtgmate"][c] = None if sub.empty else int(sub["price_cents"].min())

    if not df_parts:
        # no sources
        for src in sources:
            per_source_min[src] = {c: None for c in requested_cards}
        return OptimizeResult(
            df_cart=pd.DataFrame([]),
            sellers_used=set(),
            total_card_price_cents=0,
            total_shipping_cents=0,
            final_total_cents=0,
            missing_cards=requested_cards[:],
            requested_count=requested_count,
            found_count=0,
            per_card_min_price_cents_by_source=per_source_min
        )

    df_all = pd.concat(df_parts, ignore_index=True) if len(df_parts) > 1 else df_parts[0]

    if df_all.empty:
        for src in sources:
            per_source_min[src] = {c: None for c in requested_cards}
        return OptimizeResult(
            df_cart=pd.DataFrame([]),
            sellers_used=set(),
            total_card_price_cents=0,
            total_shipping_cents=0,
            final_total_cents=0,
            missing_cards=requested_cards[:],
            requested_count=requested_count,
            found_count=0,
            per_card_min_price_cents_by_source=per_source_min
        )

    found_set = set(df_all["card_name"].unique().tolist())
    missing_cards = [c for c in requested_cards if c not in found_set]
    found_count = requested_count - len(missing_cards)

    shipping_costs_cents = load_shipping_costs_cents(shipping_file)

    cards_in_results = df_all["card_name"].unique()
    sellers = df_all["seller"].unique()

    listing_map = {}
    buy_listing_vars = {}

    prob = LpProblem("CardCartOptimization", LpMinimize)

    for i, row in df_all.iterrows():
        max_qty = int(row["quantity"])
        var = LpVariable(f"buy_{i}", 0, max_qty, LpInteger)
        buy_listing_vars[i] = var
        listing_map[i] = row

    use_seller_vars = {
        s: LpVariable(f"use_{safe_var_name(s)}", 0, 1, LpBinary)
        for s in sellers
    }

    # Objective in cents
    prob += (
        lpSum(buy_listing_vars[i] * int(listing_map[i]["price_cents"]) for i in listing_map) +
        lpSum(use_seller_vars[s] * get_shipping_cost_for_seller_cents(s, shipping_costs_cents) for s in sellers)
    )

    # Demand constraints only for cards that appear in results (partial fill behavior)
    for card in cards_in_results:
        required_qty = int(card_quantity_map.get(card, 1))
        indices = [i for i, row in listing_map.items() if row["card_name"] == card]
        prob += lpSum(buy_listing_vars[i] for i in indices) >= required_qty

    # Link purchases to seller usage
    for s in sellers:
        indices = [i for i, row in listing_map.items() if row["seller"] == s]
        for i in indices:
            prob += buy_listing_vars[i] <= int(listing_map[i]["quantity"]) * use_seller_vars[s]

    prob.solve(PULP_CBC_CMD(msg=0))

    cart = []
    sellers_used = set()

    for i, var in buy_listing_vars.items():
        qty = int(var.varValue or 0)
        if qty <= 0:
            continue

        row = listing_map[i]
        row_data = dict(row)

        row_data["quantity"] = qty
        seller = row_data["seller"]

        ship_cents = get_shipping_cost_for_seller_cents(seller, shipping_costs_cents)
        ship_aud = float(Decimal(ship_cents) / Decimal(100))

        total_cards_from_seller = sum(
            int(buy_listing_vars[j].varValue or 0)
            for j, r in listing_map.items()
            if r["seller"] == seller
        )

        per_card_ship_aud = (Decimal(ship_cents) / Decimal(100)) / Decimal(total_cards_from_seller) if total_cards_from_seller else Decimal("0")
        price_aud = Decimal(int(row_data["price_cents"])) / Decimal(100)
        effective_total_aud = (price_aud * Decimal(qty)) + (per_card_ship_aud * Decimal(qty))

        row_data["shipping_cost"] = ship_aud
        row_data["effective_total"] = float(effective_total_aud)

        cart.append(row_data)
        sellers_used.add(seller)

    df_cart = pd.DataFrame(cart)

    total_card_price_cents = 0
    if not df_cart.empty:
        total_card_price_cents = int((df_cart["price_cents"] * df_cart["quantity"]).sum())

    total_shipping_cents = sum(get_shipping_cost_for_seller_cents(s, shipping_costs_cents) for s in sellers_used)
    final_total_cents = int(total_card_price_cents + total_shipping_cents)

    save_shipping_costs_cents(shipping_file, shipping_costs_cents)

    return OptimizeResult(
        df_cart=df_cart,
        sellers_used=sellers_used,
        total_card_price_cents=total_card_price_cents,
        total_shipping_cents=total_shipping_cents,
        final_total_cents=final_total_cents,
        missing_cards=missing_cards,
        requested_count=requested_count,
        found_count=found_count,
        per_card_min_price_cents_by_source=per_source_min
    )

def run_optimizer_for_cli(
    card_quantity_map: Dict[str, int],
    sources: List[str],
    output_csv_path: str,
    shipping_file: str = DEFAULT_SHIPPING_FILE
) -> None:
    if not card_quantity_map:
        print_colored("No cards entered. Exiting.", "red")
        sys.exit(1)

    res = optimize_internal(card_quantity_map, sources=sources, shipping_file=shipping_file)

    if res.missing_cards:
        print_colored("\nWarning: The following cards could not be found in the listings:", "yellow")
        for card in res.missing_cards:
            print_colored(f"- {card}", "yellow")
    else:
        print_colored("\nAll requested cards were found.", "green")

    if res.df_cart.empty:
        print_colored("No purchases selected by the solver.", "yellow")
        return

    df_cart = res.df_cart.copy()
    df_cart["total_cards_from_seller"] = df_cart.groupby("seller")["quantity"].transform("sum")
    df_cart = df_cart.sort_values(
        by=["total_cards_from_seller", "seller", "card_name"],
        ascending=[False, True, True]
    )

    print_colored("\n--- Optimized Cart (Sorted by Seller and Quantity) ---", "blue")

    printable_cols = [
        "card_name", "seller", "set", "condition", "finish", "language",
        "quantity", "price", "shipping_cost", "effective_total", "total_cards_from_seller", "source"
    ]
    for c in printable_cols:
        if c not in df_cart.columns:
            df_cart[c] = ""

    print(df_cart[printable_cols].to_string(index=False))

    print_colored(f"\nTotal card price: {fmt_aud(res.total_card_price_cents)}", "green")
    print_colored(f"Shipping cost ({len(res.sellers_used)} sellers): {fmt_aud(res.total_shipping_cents)}", "green")
    print_colored(f"Final total: {fmt_aud(res.final_total_cents)}", "green")

    seller_card_counts = df_cart.groupby("seller")["quantity"].sum()
    sellers_with_one_card = int((seller_card_counts == 1).sum())
    print_colored(f"Number of sellers with only one card purchased: {sellers_with_one_card}", "yellow")

    os.makedirs(os.path.dirname(output_csv_path), exist_ok=True)
    df_cart.to_csv(output_csv_path, index=False)
    print_colored(f"\nCart saved to '{output_csv_path}'", "blue")

# ----------------------------
# Phase 2 commands
# ----------------------------

def command_add_list(cfg: dict) -> None:
    index_path = cfg["lists_index_path"]
    list_folder = cfg["default_list_folder"]

    idx = load_lists_index(index_path)
    new_id = next_numeric_id(idx)

    name = input("List name (optional): ").strip()
    if not name:
        name = f"List {new_id}"

    enabled_raw = input("Enable for tracking? (true/false) [default: false]: ").strip().lower()
    if enabled_raw == "":
        enabled = False
    elif enabled_raw in ("true", "false"):
        enabled = (enabled_raw == "true")
    else:
        print_colored("Invalid value. Expected true or false. Defaulting to false.", "yellow")
        enabled = False

    qty_map = prompt_for_card_list()
    if not qty_map:
        print_colored("No cards entered. List not created.", "red")
        return

    os.makedirs(list_folder, exist_ok=True)
    filename = f"{new_id}.txt"
    list_path = os.path.join(list_folder, filename)

    unique_cards, total_qty = write_list_file(list_path, qty_map)

    idx["lists"].append({
        "id": str(new_id),
        "name": name,
        "filename": filename,
        "enabled": bool(enabled),
        "notes": ""
    })
    save_json(index_path, idx)

    print_colored(
        f"Saved list {new_id} - {name} - enabled={str(enabled).lower()} - "
        f"{unique_cards} cards - {total_qty} total qty.",
        "green"
    )

def render_table(headers: List[str], rows: List[List[str]]) -> str:
    cols = len(headers)
    widths = [len(h) for h in headers]
    for r in rows:
        for i in range(cols):
            widths[i] = max(widths[i], len(str(r[i])))

    def sep() -> str:
        parts = ["+" + ("-" * (w + 2)) for w in widths]
        return "".join(parts) + "+"

    def fmt_row(r: List[str]) -> str:
        out = "|"
        for i in range(cols):
            out += " " + str(r[i]).ljust(widths[i]) + " |"
        return out

    lines = [sep(), fmt_row(headers), sep()]
    for r in rows:
        lines.append(fmt_row(r))
    lines.append(sep())
    return "\n".join(lines)

def command_list(cfg: dict) -> None:
    index_path = cfg["lists_index_path"]
    list_folder = cfg["default_list_folder"]

    idx = load_lists_index(index_path)
    entries = idx.get("lists", [])

    def sort_key(e):
        try:
            return int(str(e.get("id")))
        except Exception:
            return 10**9

    entries = sorted(entries, key=sort_key)

    headers = ["id", "name", "enabled", "cards", "qty", "filename"]
    rows: List[List[str]] = []
    warnings: List[str] = []

    for e in entries:
        lid = str(e.get("id"))
        name = str(e.get("name", ""))
        enabled = "true" if bool(e.get("enabled", False)) else "false"
        filename = str(e.get("filename", f"{lid}.txt"))
        path = os.path.join(list_folder, filename)

        if os.path.exists(path):
            qty_map = read_list_file(path)
            cards = str(len(qty_map))
            qty = str(sum(qty_map.values()))
        else:
            cards = "-"
            qty = "-"
            warnings.append(f"Warning - missing file for list id {lid} (expected {path})")

        rows.append([lid, name, enabled, cards, qty, filename])

    print("Saved Lists")
    if rows:
        print(render_table(headers, rows))
    else:
        print_colored("No saved lists yet. Use add-list to create one.", "yellow")

    if warnings:
        print("")
        for w in warnings:
            print_colored(w, "yellow")

    print("\nUse: optimize --list <id>")

def command_enable_disable(cfg: dict, list_id: str, enabled_value: bool) -> None:
    index_path = cfg["lists_index_path"]
    idx = load_lists_index(index_path)

    entry = find_list_entry(idx, list_id)
    if entry is None:
        print_colored(f"Error - list id {list_id} not found.", "red")
        return

    entry["enabled"] = bool(enabled_value)
    save_json(index_path, idx)
    print_colored(f"List {list_id} enabled={str(enabled_value).lower()}", "green")

def command_optimize(cfg: dict, list_id: Optional[str], sources: List[str]) -> None:
    list_folder = cfg["default_list_folder"]
    out_folder = cfg["default_output_folder"]
    out_csv_path = os.path.join(out_folder, "optimized_mtg_cart_sorted.csv")

    if list_id is None:
        qty_map = prompt_for_card_list()
        run_optimizer_for_cli(qty_map, sources=sources, output_csv_path=out_csv_path, shipping_file=DEFAULT_SHIPPING_FILE)
        return

    idx = load_lists_index(cfg["lists_index_path"])
    entry = find_list_entry(idx, list_id)
    if entry is None:
        print_colored(f"Error - list id {list_id} not found.", "red")
        return

    filename = str(entry.get("filename", f"{list_id}.txt"))
    path = os.path.join(list_folder, filename)
    if not os.path.exists(path):
        print_colored(f"Error - list file not found for id {list_id} (expected {path}).", "red")
        return

    qty_map = read_list_file(path)
    unique_cards = len(qty_map)
    total_qty = sum(qty_map.values())
    enabled_str = "true" if bool(entry.get("enabled", False)) else "false"
    name = str(entry.get("name", f"List {list_id}"))

    print_colored(
        f"Loaded list {list_id} - {name} - enabled={enabled_str} - "
        f"{unique_cards} cards - {total_qty} total qty",
        "blue"
    )
    print_colored(f"Sources: {', '.join(sources)}", "blue")

    run_optimizer_for_cli(qty_map, sources=sources, output_csv_path=out_csv_path, shipping_file=DEFAULT_SHIPPING_FILE)

# ----------------------------
# SQLite tracking (Phase 3) with per-source mins
# ----------------------------

def db_connect(db_path: str) -> sqlite3.Connection:
    os.makedirs(os.path.dirname(db_path), exist_ok=True)
    conn = sqlite3.connect(db_path)
    conn.execute("PRAGMA foreign_keys = ON;")
    return conn

def table_has_column(conn: sqlite3.Connection, table: str, col: str) -> bool:
    cur = conn.execute(f"PRAGMA table_info({table});")
    cols = [r[1] for r in cur.fetchall()]
    return col in cols

def db_init(conn: sqlite3.Connection) -> None:
    # Create base tables if missing
    conn.execute("""
    CREATE TABLE IF NOT EXISTS list_daily (
        date TEXT NOT NULL,
        list_id TEXT NOT NULL,
        requested_count INTEGER NOT NULL,
        found_count INTEGER NOT NULL,
        optimized_card_total_cents INTEGER NOT NULL,
        optimized_shipping_total_cents INTEGER NOT NULL,
        optimized_final_total_cents INTEGER NOT NULL,
        sellers_used_count INTEGER NOT NULL,
        missing_cards_json TEXT NOT NULL,
        sources_json TEXT NOT NULL DEFAULT '["trademagic"]',
        PRIMARY KEY (date, list_id)
    );
    """)

    # Migration for older list_daily without sources_json
    if not table_has_column(conn, "list_daily", "sources_json"):
        conn.execute("""ALTER TABLE list_daily ADD COLUMN sources_json TEXT NOT NULL DEFAULT '["trademagic"]';""")

    # card_daily migration: old schema had no "source"
    if table_has_column(conn, "card_daily", "card_name") and not table_has_column(conn, "card_daily", "source"):
        # rename old table
        conn.execute("ALTER TABLE card_daily RENAME TO card_daily_old;")

    conn.execute("""
    CREATE TABLE IF NOT EXISTS card_daily (
        date TEXT NOT NULL,
        list_id TEXT NOT NULL,
        source TEXT NOT NULL,
        card_name TEXT NOT NULL,
        found INTEGER NOT NULL,
        min_price_cents INTEGER NULL,
        PRIMARY KEY (date, list_id, source, card_name)
    );
    """)

    # If we have a renamed old table, migrate data into new schema
    cur = conn.execute("""
    SELECT name FROM sqlite_master WHERE type='table' AND name='card_daily_old';
    """)
    if cur.fetchone() is not None:
        conn.execute("""
        INSERT OR IGNORE INTO card_daily (date, list_id, source, card_name, found, min_price_cents)
        SELECT date, list_id, 'trademagic' AS source, card_name, found, min_price_cents
        FROM card_daily_old;
        """)
        conn.execute("DROP TABLE card_daily_old;")

    conn.execute("CREATE INDEX IF NOT EXISTS idx_list_daily_listid_date ON list_daily(list_id, date);")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_card_daily_listid_date ON card_daily(list_id, date);")
    conn.execute("CREATE INDEX IF NOT EXISTS idx_card_daily_listid_date_source ON card_daily(list_id, date, source);")

    # Recreate view with sources_json included
    conn.execute("DROP VIEW IF EXISTS list_daily_view;")
    conn.execute("""
    CREATE VIEW list_daily_view AS
    SELECT
      date,
      list_id,
      requested_count,
      found_count,
      CASE
        WHEN requested_count = 0 THEN NULL
        ELSE CAST(found_count AS REAL) / requested_count
      END AS fill_ratio,
      optimized_card_total_cents / 100.0 AS optimized_card_total_aud,
      optimized_shipping_total_cents / 100.0 AS optimized_shipping_total_aud,
      optimized_final_total_cents / 100.0 AS optimized_final_total_aud,
      sellers_used_count,
      missing_cards_json,
      sources_json
    FROM list_daily;
    """)

    conn.commit()

def db_upsert_tracking(
    conn: sqlite3.Connection,
    date_str: str,
    list_id: str,
    sources: List[str],
    res: OptimizeResult
) -> None:
    missing_json = json.dumps(res.missing_cards, ensure_ascii=False)
    sources_json = json.dumps(sources, ensure_ascii=False)

    conn.execute("""
    INSERT INTO list_daily (
        date, list_id, requested_count, found_count,
        optimized_card_total_cents, optimized_shipping_total_cents, optimized_final_total_cents,
        sellers_used_count, missing_cards_json, sources_json
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    ON CONFLICT(date, list_id) DO UPDATE SET
        requested_count=excluded.requested_count,
        found_count=excluded.found_count,
        optimized_card_total_cents=excluded.optimized_card_total_cents,
        optimized_shipping_total_cents=excluded.optimized_shipping_total_cents,
        optimized_final_total_cents=excluded.optimized_final_total_cents,
        sellers_used_count=excluded.sellers_used_count,
        missing_cards_json=excluded.missing_cards_json,
        sources_json=excluded.sources_json
    ;
    """, (
        date_str, str(list_id),
        int(res.requested_count), int(res.found_count),
        int(res.total_card_price_cents), int(res.total_shipping_cents), int(res.final_total_cents),
        int(len(res.sellers_used)), missing_json, sources_json
    ))

    # Per-source mins
    for src, per_card in res.per_card_min_price_cents_by_source.items():
        for card_name, min_cents in per_card.items():
            found = 0 if min_cents is None else 1
            conn.execute("""
            INSERT INTO card_daily (date, list_id, source, card_name, found, min_price_cents)
            VALUES (?, ?, ?, ?, ?, ?)
            ON CONFLICT(date, list_id, source, card_name) DO UPDATE SET
                found=excluded.found,
                min_price_cents=excluded.min_price_cents
            ;
            """, (date_str, str(list_id), str(src), str(card_name), int(found), (int(min_cents) if min_cents is not None else None)))

    conn.commit()

def is_qualified(found_count: int, requested_count: int) -> bool:
    if requested_count <= 0:
        return False
    return (found_count * QUALIFIED_FILL_DEN) >= (requested_count * QUALIFIED_FILL_NUM)

def color_for_fill(found_count: int, requested_count: int) -> str:
    if requested_count <= 0:
        return "yellow"
    if found_count == requested_count:
        return "green"
    if is_qualified(found_count, requested_count):
        return "yellow"
    return "red"

def color_for_delta(delta_cents: Optional[int]) -> str:
    if delta_cents is None:
        return "yellow"
    if abs(delta_cents) <= DELTA_NOISE_BAND_CENTS:
        return "yellow"
    return "green" if delta_cents < 0 else "red"

def compute_fill_percent(found_count: int, requested_count: int) -> Optional[float]:
    if requested_count <= 0:
        return None
    return (found_count / requested_count) * 100.0

def dashboard_for_list(conn: sqlite3.Connection, list_id: str, list_name: str, days: int) -> None:
    days = int(days)
    if days <= 0:
        days = 30

    cur = conn.cursor()
    cur.execute("SELECT MAX(date) FROM list_daily WHERE list_id = ?", (str(list_id),))
    row = cur.fetchone()
    if not row or row[0] is None:
        print_colored(f"List {list_id} - {list_name} ({days}d)", "blue")
        print_colored("No history.", "yellow")
        print("")
        return

    latest_date = row[0]

    cur.execute("""
    SELECT date, requested_count, found_count, optimized_final_total_cents, sources_json
    FROM list_daily
    WHERE list_id = ?
      AND date >= date(?, ?)
    ORDER BY date ASC
    """, (str(list_id), latest_date, f"-{days - 1} days"))
    rows = cur.fetchall()

    if not rows:
        print_colored(f"List {list_id} - {list_name} ({days}d)", "blue")
        print_colored("No history in the selected range.", "yellow")
        print("")
        return

    cur_date, y, x, cur_total, sources_json = rows[-1]
    y, x, cur_total = int(y), int(x), int(cur_total)
    sources_used = ""
    try:
        sources_used = ", ".join(json.loads(sources_json))
    except Exception:
        sources_used = ""

    prev_total = None
    if len(rows) >= 2:
        prev_total = int(rows[-2][3])
    delta_1d = (cur_total - prev_total) if prev_total is not None else None

    prev_records = [int(r[3]) for r in rows[:-1]]
    take = prev_records[-7:] if len(prev_records) >= 7 else prev_records
    avg_7 = None
    if len(take) > 0:
        avg_7 = int(round(sum(take) / len(take)))
    delta_7d = (cur_total - avg_7) if avg_7 is not None else None

    qualified_totals = []
    any_totals = []
    for d, ry, rx, t, _sj in rows:
        ry_i, rx_i, t_i = int(ry), int(rx), int(t)
        any_totals.append((t_i, d, ry_i, rx_i))
        if is_qualified(rx_i, ry_i):
            qualified_totals.append((t_i, d, ry_i, rx_i))

    using_qualified = True
    if qualified_totals:
        min_total, min_date, _, _ = min(qualified_totals, key=lambda z: z[0])
        max_total, max_date, _, _ = max(qualified_totals, key=lambda z: z[0])
    else:
        using_qualified = False
        min_total, min_date, _, _ = min(any_totals, key=lambda z: z[0])
        max_total, max_date, _, _ = max(any_totals, key=lambda z: z[0])

    fill_ok = is_qualified(x, y)
    status = "OK"
    status_color = "blue"

    if y > 0 and not fill_ok:
        status = "LOW FILL"
        status_color = "red"
    else:
        if using_qualified and cur_total == min_total:
            status = "NEW LOW"
            status_color = "green"
        elif cur_total <= (min_total + NEAR_LOW_THRESHOLD_CENTS):
            status = "NEAR LOW"
            status_color = "yellow"
        else:
            if delta_7d is not None and abs(delta_7d) > DELTA_NOISE_BAND_CENTS:
                status = "BELOW 7D AVG" if delta_7d < 0 else "ABOVE 7D AVG"
                status_color = "green" if delta_7d < 0 else "red"
            else:
                status = "STABLE"
                status_color = "yellow"

    fill_pct = compute_fill_percent(x, y)
    fill_str = f"{x}/{y}" if y > 0 else "n/a"
    fill_pct_str = f"{fill_pct:.1f}%" if fill_pct is not None else "n/a"

    print_colored(f"List {list_id} - {list_name} ({days}d)", "blue")
    if sources_used:
        print_colored(f"Sources: {sources_used}", "blue")
    print(f"Current: {fmt_aud(cur_total)}   Fill: {fill_str} ({fill_pct_str})")

    delta_1d_str = fmt_aud(delta_1d) if delta_1d is not None else "n/a"
    delta_7d_str = fmt_aud(delta_7d) if delta_7d is not None else "n/a"

    print_colored(f"Δ1d: {delta_1d_str}", color_for_delta(delta_1d))
    print_colored(f"Δ7d avg: {delta_7d_str}", color_for_delta(delta_7d))

    label = f"{days}d min (qualified)" if using_qualified else f"{days}d min (any)"
    label2 = f"{days}d max (qualified)" if using_qualified else f"{days}d max (any)"
    print(f"{label}: {fmt_aud(min_total)} on {min_date}   {label2}: {fmt_aud(max_total)}")
    print_colored(f"Status: {status}", status_color)
    print("")

def command_track(cfg: dict, list_id: Optional[str], enabled_only: bool, sources: List[str]) -> None:
    idx = load_lists_index(cfg["lists_index_path"])
    list_folder = cfg["default_list_folder"]
    db_path = cfg["tracking_db_path"]

    os.makedirs(os.path.dirname(db_path), exist_ok=True)
    date_str = get_local_date_brisbane()

    entries = idx.get("lists", [])
    targets: List[dict] = []
    if enabled_only:
        targets = [e for e in entries if bool(e.get("enabled", False))]
    else:
        if list_id is None:
            print_colored("Error - track requires --list <id> or --enabled", "red")
            return
        e = find_list_entry(idx, list_id)
        if e is None:
            print_colored(f"Error - list id {list_id} not found.", "red")
            return
        targets = [e]

    if not targets:
        print_colored("No lists to track.", "yellow")
        return

    conn = db_connect(db_path)
    db_init(conn)

    for e in sorted(targets, key=lambda z: int(str(z.get("id", "999999")))):
        lid = str(e.get("id"))
        name = str(e.get("name", f"List {lid}"))
        filename = str(e.get("filename", f"{lid}.txt"))
        path = os.path.join(list_folder, filename)

        if not os.path.exists(path):
            print_colored(f"Error - list file not found for id {lid} (expected {path}).", "red")
            continue

        try:
            qty_map = read_list_file(path)
            res = optimize_internal(qty_map, sources=sources, shipping_file=DEFAULT_SHIPPING_FILE)
            db_upsert_tracking(conn, date_str, lid, sources=sources, res=res)

            fill_color = color_for_fill(res.found_count, res.requested_count)
            fill_pct = compute_fill_percent(res.found_count, res.requested_count)
            fill_pct_str = f"{fill_pct:.1f}%" if fill_pct is not None else "n/a"

            print_colored(f"Tracked {date_str} - list {lid} - {name}", "green")
            print_colored(f"Sources: {', '.join(sources)}", "blue")
            print_colored(f"Fill: {res.found_count}/{res.requested_count} ({fill_pct_str})", fill_color)
            print(f"Total: {fmt_aud(res.final_total_cents)}")
            if res.missing_cards:
                print_colored(f"Missing: {len(res.missing_cards)} card(s)", "yellow")
            print("")
        except Exception as ex:
            print_colored(f"Error tracking list {lid} - {name}: {ex}", "red")
            print("")

    conn.close()

def command_history(cfg: dict, list_id: Optional[str], enabled_only: bool, days: int) -> None:
    idx = load_lists_index(cfg["lists_index_path"])
    db_path = cfg["tracking_db_path"]

    if not os.path.exists(db_path):
        print_colored("No tracking database found. Run track first.", "yellow")
        return

    conn = db_connect(db_path)
    db_init(conn)

    entries = idx.get("lists", [])
    targets: List[dict] = []
    if enabled_only:
        targets = [e for e in entries if bool(e.get("enabled", False))]
    else:
        if list_id is None:
            print_colored("Error - history requires --list <id> or --enabled", "red")
            conn.close()
            return
        e = find_list_entry(idx, list_id)
        if e is None:
            print_colored(f"Error - list id {list_id} not found.", "red")
            conn.close()
            return
        targets = [e]

    if not targets:
        print_colored("No lists selected.", "yellow")
        conn.close()
        return

    for e in sorted(targets, key=lambda z: int(str(z.get("id", "999999")))):
        lid = str(e.get("id"))
        name = str(e.get("name", f"List {lid}"))
        dashboard_for_list(conn, lid, name, int(days))

    conn.close()

# ----------------------------
# CLI
# ----------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="TradeMagic Cart Optimizer", add_help=True)
    sub = p.add_subparsers(dest="command", required=True)

    sub.add_parser("add-list", help="Create a new saved list (interactive).")
    sub.add_parser("list", help="Show saved lists.")

    opt = sub.add_parser("optimize", help="Optimize a cart (interactive by default).")
    opt.add_argument("--list", dest="list_id", help="Use a saved list id (numeric).", default=None)
    opt.add_argument("--sources", dest="sources", default="trademagic,mtgmate",
                     help="Comma-separated sources: trademagic,mtgmate (default both).")

    en = sub.add_parser("enable", help="Enable a list for tracking (flag).")
    en.add_argument("--list", dest="list_id", required=True, help="Saved list id (numeric).")

    dis = sub.add_parser("disable", help="Disable a list for tracking (flag).")
    dis.add_argument("--list", dest="list_id", required=True, help="Saved list id (numeric).")

    track = sub.add_parser("track", help="Track prices (snapshot + optimize) and write to SQLite.")
    tg = track.add_mutually_exclusive_group(required=True)
    tg.add_argument("--list", dest="list_id", help="Track a single saved list id (numeric).")
    tg.add_argument("--enabled", dest="enabled", action="store_true", help="Track all lists with enabled=true.")
    track.add_argument("--sources", dest="sources", default="trademagic,mtgmate",
                       help="Comma-separated sources: trademagic,mtgmate (default both).")

    hist = sub.add_parser("history", help="Show history dashboard from SQLite.")
    hg = hist.add_mutually_exclusive_group(required=True)
    hg.add_argument("--list", dest="list_id", help="Show history for a single saved list id (numeric).")
    hg.add_argument("--enabled", dest="enabled", action="store_true", help="Show history for all lists with enabled=true.")
    hist.add_argument("--days", dest="days", type=int, default=30, help="History window in days (default 30).")

    return p

def main() -> None:
    cfg = load_config(DEFAULT_CONFIG_PATH)

    os.makedirs(cfg["default_list_folder"], exist_ok=True)
    os.makedirs(cfg["default_output_folder"], exist_ok=True)

    db_path = cfg.get("tracking_db_path", DEFAULT_TRACKING_DB)
    if db_path and os.path.dirname(db_path):
        os.makedirs(os.path.dirname(db_path), exist_ok=True)

    parser = build_parser()
    args = parser.parse_args()

    if args.command == "add-list":
        command_add_list(cfg)
        return

    if args.command == "list":
        command_list(cfg)
        return

    if args.command == "enable":
        command_enable_disable(cfg, args.list_id, True)
        return

    if args.command == "disable":
        command_enable_disable(cfg, args.list_id, False)
        return

    if args.command in ("optimize", "track"):
        try:
            sources = parse_sources_arg(getattr(args, "sources", "trademagic,mtgmate"))
        except ValueError as e:
            print_colored(str(e), "red")
            sys.exit(1)

        if args.command == "optimize":
            command_optimize(cfg, args.list_id, sources=sources)
            return

        if args.command == "track":
            command_track(cfg, getattr(args, "list_id", None), bool(getattr(args, "enabled", False)), sources=sources)
            return

    if args.command == "history":
        command_history(cfg, getattr(args, "list_id", None), bool(getattr(args, "enabled", False)), int(getattr(args, "days", 30)))
        return

    parser.print_help()

if __name__ == "__main__":
    main()