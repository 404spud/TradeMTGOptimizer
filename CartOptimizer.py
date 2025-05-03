import requests
from bs4 import BeautifulSoup
import pandas as pd
import re
import sys
import os
import json
from pulp import LpProblem, LpMinimize, LpVariable, lpSum, LpBinary, PULP_CBC_CMD

# Path to the JSON file that will store shipping costs
shipping_file = 'shipping_costs.json'

# Function to print colored text with Rose Pine colors
def print_colored(text, color_code):
    COLORS = {
        "red": "\033[38;5;209m",
        "green": "\033[38;5;32m",
        "yellow": "\033[38;5;229m",
        "blue": "\033[38;5;153m",
        "reset": "\033[38;5;255m"
    }
    print(f"{COLORS.get(color_code, COLORS['reset'])}{text}{COLORS['reset']}")

# --- Step 1: Load Existing Shipping Costs (if they exist) ---
if os.path.exists(shipping_file):
    with open(shipping_file, 'r') as file:
        shipping_costs = json.load(file)
else:
    shipping_costs = {}

# Function to get shipping cost for a seller
def get_shipping_cost_for_seller(seller):
    if seller in shipping_costs:
        return shipping_costs[seller]
    print_colored(f"Enter the shipping cost for seller '{seller}' (in AUD): ", "blue")
    while True:
        try:
            shipping_cost = float(input(f"Shipping cost for seller '{seller}': "))
            shipping_costs[seller] = shipping_cost
            return shipping_cost
        except ValueError:
            print("Invalid input! Please enter a valid numeric shipping cost.")

# --- Step 2: Get Card List with Quantities from User ---
print_colored("Enter your card list with quantities (e.g. '2 Lightning Bolt'), one per line. When done, enter an empty line:", "blue")
card_quantity_map = {}
card_list = []

pattern = re.compile(r'^(\d+)\s+(.+)$')
while True:
    line = input()
    if line.strip() == "":
        break
    match = pattern.match(line.strip())
    if match:
        qty = int(match.group(1))
        name = match.group(2).strip()
        card_quantity_map[name] = qty
        card_list.append(name)
    else:
        print_colored(f"Skipping malformed line: {line}", "yellow")

if not card_list:
    print_colored("No cards entered. Exiting.", "red")
    sys.exit()

# --- Step 3: Submit card list to the website ---
url = "https://trademagic.com.au/bulksearch.php"

payload = {
    "multilineData": "\n".join(card_list)
}

session = requests.Session()
response = session.post(url, data=payload)

if response.status_code != 200:
    print_colored(f"Failed to fetch data from the site. Status code: {response.status_code}", "red")
    sys.exit()

# --- Step 4: Parse the results ---
soup = BeautifulSoup(response.content, "html.parser")
table = soup.find("table", {"id": "myTable"})

if table is None:
    print_colored("No results table found. Check your card names.", "red")
    sys.exit()

rows = table.find_all("tr")

listings = []
for row in rows[1:]:
    cols = row.find_all("td")
    if len(cols) < 9:
        continue
    try:
        card_name = cols[0].text.strip()
        seller = cols[1].text.strip()
        set_name = cols[4].find('img')['title'].strip() if cols[4].find('img') else cols[4].text.strip()
        condition = cols[5].find('i')['title'].strip() if cols[5].find('i') else cols[5].text.strip()
        language = cols[6].text.strip()
        quantity = int(cols[7].text.strip())
        price_text = cols[8].text.strip()
        price = float(re.sub(r'[^\d.]', '', price_text))

        listings.append({
            'card_name': card_name,
            'seller': seller,
            'set': set_name,
            'condition': condition,
            'language': language,
            'quantity': quantity,
            'price': price
        })
    except Exception:
        continue

df_listings = pd.DataFrame(listings)

if df_listings.empty:
    print_colored("No valid listings found.", "red")
    sys.exit()

# --- Step 5: Check for Missing Cards ---
missing_cards = [card for card in card_list if card not in df_listings['card_name'].unique()]

if missing_cards:
    print_colored("\nWarning: The following cards could not be found in the listings:", "yellow")
    for card in missing_cards:
        print_colored(f"- {card}", "yellow")
else:
    print_colored("\nAll requested cards were found.", "green")

# --- Step 6: Bulk Optimization Algorithm ---
cards = df_listings['card_name'].unique()
sellers = df_listings['seller'].unique()

listing_map = {}
buy_listing_vars = []
prob = LpProblem("CardCartOptimization", LpMinimize)

for i, row in df_listings.iterrows():
    var = LpVariable(f"buy_{i}", 0, 1, LpBinary)
    buy_listing_vars.append(var)
    listing_map[i] = row

use_seller_vars = {s: LpVariable(f"use_{s}", 0, 1, LpBinary) for s in sellers}

prob += lpSum(
    buy_listing_vars[i] * listing_map[i]['price']
    for i in listing_map
) + lpSum(
    use_seller_vars[s] * get_shipping_cost_for_seller(s)
    for s in sellers
)

for card in cards:
    required_qty = card_quantity_map.get(card, 1)
    indices = [i for i, row in listing_map.items() if row['card_name'] == card]
    prob += lpSum(buy_listing_vars[i] * listing_map[i]['quantity'] for i in indices) >= required_qty

for s in sellers:
    indices = [i for i, row in listing_map.items() if row['seller'] == s]
    for i in indices:
        prob += buy_listing_vars[i] <= use_seller_vars[s]

prob.solve(PULP_CBC_CMD(msg=0))

cart = []
sellers_used = set()
for i, var in enumerate(buy_listing_vars):
    if var.varValue == 1:
        row = listing_map[i]
        row_data = dict(row)
        row_data['shipping_cost'] = get_shipping_cost_for_seller(row_data['seller'])
        row_data['effective_total'] = row_data['price'] + row_data['shipping_cost']
        cart.append(row_data)
        sellers_used.add(row_data['seller'])

df_cart = pd.DataFrame(cart)

df_cart['total_cards_from_seller'] = df_cart.groupby('seller')['quantity'].transform('sum')
df_cart = df_cart.sort_values(by=['total_cards_from_seller', 'seller', 'card_name'], ascending=[False, True, True])
df_cart = df_cart.fillna({'shipping_cost': '-', 'effective_total': '-'})

print_colored("\n--- Optimized Cart (Sorted by Seller and Quantity, NaN Replaced with Blank) ---", "blue")
print(df_cart.to_string(index=False))

total_card_price = df_cart['price'].sum()
unique_sellers = df_cart['seller'].unique()
total_shipping = sum(get_shipping_cost_for_seller(seller) for seller in unique_sellers)
final_total = total_card_price + total_shipping

print_colored(f"\nTotal card price: ${total_card_price:.2f}", "green")
print_colored(f"Shipping cost ({len(unique_sellers)} sellers): ${total_shipping:.2f}", "green")
print_colored(f"Final total: ${final_total:.2f}", "green")

seller_card_counts = df_cart.groupby('seller')['quantity'].sum()
sellers_with_one_card = (seller_card_counts == 1).sum()

print_colored(f"Number of sellers with only one card purchased: {sellers_with_one_card}", "yellow")

df_cart.to_csv('optimized_mtg_cart_sorted.csv', index=False)
print_colored("\nCart saved to 'optimized_mtg_cart_sorted.csv' (sorted by seller and quantity, NaN replaced with blank)", "blue")

with open(shipping_file, 'w') as file:
    json.dump(shipping_costs, file)
