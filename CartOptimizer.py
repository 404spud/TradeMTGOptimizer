import requests
from bs4 import BeautifulSoup
import pandas as pd
import re
import sys
import os
import json

# Path to the JSON file that will store shipping costs
shipping_file = 'shipping_costs.json'

# Function to print colored text with Rose Pine colors
def print_colored(text, color_code):
    # Rose Pine color codes
    COLORS = {
        "red": "\033[38;5;209m",       # #eb6f92
        "green": "\033[38;5;32m",      # #31748f
        "yellow": "\033[38;5;229m",    # #f6c177
        "blue": "\033[38;5;153m",      # #9ccfd8
        "reset": "\033[38;5;255m"      # #e0def4
    }
    print(f"{COLORS.get(color_code, COLORS['reset'])}{text}{COLORS['reset']}")

# Step 1: Load Existing Shipping Costs (if they exist)
if os.path.exists(shipping_file):
    with open(shipping_file, 'r') as file:
        shipping_costs = json.load(file)
else:
    shipping_costs = {}

# Function to get shipping cost for a seller (asks the user and stores it)
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

# --- Step 2: Get Card List from User ---
print_colored("Enter your card list (one per line). When done, enter an empty line:", "blue")
card_list = []
while True:
    line = input()
    if line.strip() == "":
        break
    card_list.append(line.strip())

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
        continue  # skip if not a valid card row

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
    except Exception as e:
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
cart = []
sellers_used = set()

for card in df_listings['card_name'].unique():
    card_options = df_listings[df_listings['card_name'] == card]
    
    preferred_sellers = card_options[card_options['seller'].isin(sellers_used)]
    
    if not preferred_sellers.empty:
        best_option = preferred_sellers.loc[preferred_sellers['price'].idxmin()]
    else:
        card_options = card_options.copy()
        
        # Add shipping costs to the total cost per card
        card_options['shipping_cost'] = card_options['seller'].apply(get_shipping_cost_for_seller)
        card_options['effective_total'] = card_options['price'] + card_options['shipping_cost']
        
        best_option = card_options.loc[card_options['effective_total'].idxmin()]
        sellers_used.add(best_option['seller'])
    
    cart.append(best_option)

df_cart = pd.DataFrame(cart)

# --- Step 7: Summarize, Sort, and Save ---
total_card_price = df_cart['price'].sum()
total_shipping = df_cart['shipping_cost'].sum()
final_total = total_card_price + total_shipping

# Sort by seller before saving
df_cart = df_cart.sort_values(by=['seller', 'card_name'])

# Display summary to terminal
print_colored("\n--- Optimized Cart (Sorted by Seller) ---", "blue")
print(df_cart)
print_colored(f"\nTotal card price: ${total_card_price:.2f}", "green")
print_colored(f"Shipping cost: ${total_shipping:.2f}", "green")
print_colored(f"Final total: ${final_total:.2f}", "green")

# Save to CSV
df_cart.to_csv('optimized_mtg_cart.csv', index=False)
print_colored("\nCart saved to 'optimized_mtg_cart.csv' (sorted by seller)", "blue")

# Step 8: Save the updated shipping costs back to the file
with open(shipping_file, 'w') as file:
    json.dump(shipping_costs, file)
