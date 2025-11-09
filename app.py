from flask import Flask, render_template, session, request
from flask_socketio import SocketIO, emit, join_room
import secrets
from enum import Enum
import random
import time
import os
import json
import traceback

app = Flask(__name__)
app.config['SECRET_KEY'] = secrets.token_hex(16)
socketio = SocketIO(app, cors_allowed_origins="*", ping_timeout=60, ping_interval=25)

games = {}
SAVE_DIR = 'saved_games'
if not os.path.exists(SAVE_DIR):
    os.makedirs(SAVE_DIR)

class Rank(Enum):
    THREE = (3, '3')
    FOUR = (4, '4')
    FIVE = (5, '5')
    SIX = (6, '6')
    SEVEN = (7, '7')
    EIGHT = (8, '8')
    NINE = (9, '9')
    TEN = (10, '10')
    JACK = (11, 'J')
    QUEEN = (12, 'Q')
    KING = (13, 'K')
    ACE = (14, 'A')
    TWO = (15, '2')

class Suit(Enum):
    SPADES = '♠'
    HEARTS = '♥'
    DIAMONDS = '♦'
    CLUBS = '♣'

class ExchangeState(Enum):
    WAITING_PRESIDENT = 1
    WAITING_ASSHOLE = 2
    WAITING_VP = 3
    WAITING_VA = 4
    COMPLETE = 5

class Card:
    def __init__(self, rank, suit):
        self.rank = rank
        self.suit = suit
        self.display = f"{rank.value[1]}{suit.value}"

    def __repr__(self):
        return self.display

    @staticmethod
    def from_str(card_str):
        suit_map = {'♠': Suit.SPADES, '♥': Suit.HEARTS, '♦': Suit.DIAMONDS, '♣': Suit.CLUBS}
        rank_map = {'3': Rank.THREE, '4': Rank.FOUR, '5': Rank.FIVE, '6': Rank.SIX, '7': Rank.SEVEN,
                    '8': Rank.EIGHT, '9': Rank.NINE, '10': Rank.TEN, 'J': Rank.JACK, 'Q': Rank.QUEEN,
                    'K': Rank.KING, 'A': Rank.ACE, '2': Rank.TWO}
        suit_char = card_str[-1]
        rank_str = card_str[:-1]
        return Card(rank_map[rank_str], suit_map[suit_char])

class Player:
    def __init__(self, player_id, name, is_cpu=False):
        self.player_id = player_id
        self.name = name
        self.is_cpu = is_cpu
        self.hand = []
        self.role = 'Citizen'
        self.finished_position = None
        self.passed = False

    def add_card(self, card):
        self.hand.append(card)
        self.hand.sort(key=lambda c: c.rank.value[0])

    def remove_card(self, card):
        if card in self.hand:
            self.hand.remove(card)
            return True
        return False

    def has_cards(self):
        return len(self.hand) > 0

def is_valid_meld(cards):
    """Check if cards form a valid meld. Returns (is_valid, meld_type_str)"""
    if not cards or len(cards) == 0:
        return False, "No cards"
    if len(cards) > 5:
        return False, "Too many cards (max 5)"
    if len(cards) == 1:
        return True, "SINGLE"

    ranks = [c.rank for c in cards]
    if all(r == ranks[0] for r in ranks):
        if len(cards) == 2:
            return True, "PAIR"
        elif len(cards) == 3:
            return True, "TRIPLE"
        elif len(cards) == 4:
            return True, "QUAD"
        else:
            return False, "Invalid same-rank meld"

    if len(cards) >= 3:
        rank_values = sorted([c.rank.value[0] for c in cards])
        is_consecutive = all(rank_values[i] + 1 == rank_values[i+1] for i in range(len(rank_values)-1))
        if is_consecutive:
            return True, f"RUN({len(cards)})"

    return False, "Invalid meld"

def get_meld_type(cards):
    """Get the type of meld. Returns None if invalid."""
    valid, mtype = is_valid_meld(cards)
    return mtype if valid else None

def compare_melds(played_meld, table_meld):
    """Check if played_meld beats table_meld. Returns (is_valid, reason_str)"""
    ptype = get_meld_type(played_meld)
    ttype = get_meld_type(table_meld)

    if not ptype or not ttype:
        return False, "Invalid meld format"
    if ptype != ttype:
        return False, f"Meld type mismatch: {ptype} vs {ttype}"

    if ptype == "SINGLE":
        if played_meld[0].rank.value[0] > table_meld[0].rank.value[0]:
            return True, "Valid single"
        else:
            return False, "Card must be higher rank"

    if ptype in ["PAIR", "TRIPLE", "QUAD"]:
        played_rank = max(c.rank.value[0] for c in played_meld)
        table_rank = max(c.rank.value[0] for c in table_meld)
        if played_rank > table_rank:
            return True, f"Valid {ptype}"
        else:
            return False, f"{ptype} must be higher rank"

    if ptype.startswith("RUN"):
        if len(played_meld) != len(table_meld):
            return False, f"Run must be same length: {len(table_meld)} cards"
        played_min = min(c.rank.value[0] for c in played_meld)
        table_min = min(c.rank.value[0] for c in table_meld)
        if played_min > table_min:
            return True, f"Valid RUN({len(played_meld)})"
        else:
            return False, f"Run must start with higher card"

    return False, "Unknown error"

class Game:
    def __init__(self, game_id):
        self.game_id = game_id
        self.players = {}
        self.player_order = []
        self.original_player_order = []
        self.current_player_idx = 0
        self.lead_player_idx = 0
        self.table_cards = []
        self.table_meld_type = None
        self.finished_count = 0
        self.state = 'waiting'
        self.round_num = 0
        self.exchange_state_enum = None
        self.pending_exchanges = {}
        self.human_player_id = None
        self.cpu_playing = False
        self._showing_2 = False

    def add_player(self, player_id, name, is_cpu=False):
        if len(self.players) >= 4:
            return False
        player = Player(player_id, name, is_cpu)
        self.players[player_id] = player
        if not is_cpu:
            self.human_player_id = player_id
        return True

    def find_player_by_name(self, player_name):
        for player_id, player in self.players.items():
            if player.name.lower() == player_name.lower():
                return player_id, player
        return None, None

    def rejoin_player(self, old_player_id, new_player_id, name):
        """Rejoin with new connection ID, keeping original seat."""
        old_player = self.players.get(old_player_id)
        if not old_player or old_player_id not in self.original_player_order:
            return False

        print(f"[REJOIN] {name} rejoining: {old_player_id} -> {new_player_id}")
        old_player.player_id = new_player_id
        old_player.is_cpu = False
        self.players[new_player_id] = old_player
        del self.players[old_player_id]

        pos = self.original_player_order.index(old_player_id)
        self.original_player_order[pos] = new_player_id
        print(f"[REJOIN] Original seat {pos}: {old_player_id} -> {new_player_id}")

        if old_player_id in self.player_order:
            pos = self.player_order.index(old_player_id)
            self.player_order[pos] = new_player_id
            print(f"[REJOIN] Current order seat {pos}: {old_player_id} -> {new_player_id}")

        self.human_player_id = new_player_id
        return True

    def cleanup_player_order(self):
        before = self.player_order.copy()
        removed_count = 0
        for i in range(min(self.current_player_idx, len(self.player_order))):
            if i < len(self.player_order) and self.player_order[i] not in self.players:
                removed_count += 1

        self.player_order = [pid for pid in self.player_order if pid in self.players]
        if removed_count > 0:
            self.current_player_idx = max(0, self.current_player_idx - removed_count)

        if before != self.player_order:
            print(f"[CLEANUP] player_order: {before} -> {self.player_order}")

    def can_start(self):
        return len(self.players) >= 2

    def start_round(self, preserve_roles=False):
        self.round_num += 1

        if self.round_num == 1:
            deck = []
            for rank in Rank:
                for suit in Suit:
                    deck.append(Card(rank, suit))
            random.shuffle(deck)

            for player in self.players.values():
                player.hand = []
                player.finished_position = None
                player.passed = False

            self.player_order = list(self.players.keys())
            self.original_player_order = list(self.players.keys())
            print(f"[START] Original seating: {[self.players[pid].name for pid in self.original_player_order]}")

            for i, card in enumerate(deck):
                idx = i % len(self.player_order)
                self.players[self.player_order[idx]].add_card(card)
        else:
            for player in self.players.values():
                player.finished_position = None
                player.passed = False
            self.player_order = self.original_player_order.copy()
            print(f"[START] Restoring seating: {[self.players[pid].name for pid in self.player_order]}")

        if not preserve_roles:
            for p in self.players.values():
                p.role = 'Citizen'

        self.current_player_idx = 0
        self.lead_player_idx = 0
        self.table_cards = []
        self.table_meld_type = None
        self.finished_count = 0
        self.state = 'playing'
        self.exchange_state_enum = None
        self.pending_exchanges = {}
        self.cpu_playing = False
        self._showing_2 = False

    def get_current_player(self):
        if not self.player_order or self.current_player_idx >= len(self.player_order):
            return None
        current_id = self.player_order[self.current_player_idx]
        return self.players.get(current_id)

    def next_player(self):
        attempts = 0
        max_attempts = len(self.player_order) * 2

        while attempts < max_attempts:
            self.current_player_idx = (self.current_player_idx + 1) % len(self.player_order)
            p = self.get_current_player()

            if not p:
                attempts += 1
                continue

            if not p.has_cards():
                p.passed = True
                print(f"[NEXT_PLAYER] {p.name} has no cards, auto-passing")
                attempts += 1
                continue

            print(f"[NEXT_PLAYER] Next player: {p.name}")
            return

        print(f"[WARNING] next_player() exhausted all attempts")

    def play_cards(self, player_id, card_displays):
        player = self.players.get(player_id)
        current = self.get_current_player()

        if not current or current.player_id != player_id:
            return {'ok': False, 'msg': 'Not your turn'}

        cards = []
        for display in card_displays:
            found = None
            for c in player.hand:
                if str(c) == display:
                    found = c
                    break
            if not found:
                return {'ok': False, 'msg': f'Card {display} not found'}
            cards.append(found)

        if not cards:
            return {'ok': False, 'msg': 'No cards selected'}

        valid_meld, meld_type_str = is_valid_meld(cards)
        if not valid_meld:
            return {'ok': False, 'msg': f'Invalid meld: {meld_type_str}'}

        if cards[0].rank == Rank.TWO:
            for c in cards:
                player.remove_card(c)

            if not self.table_cards:
                self.lead_player_idx = self.current_player_idx

            self.table_cards = cards
            self.table_meld_type = "SINGLE"

            for p in self.players.values():
                p.passed = False

            if not player.has_cards():
                self.finished_count += 1
                player.finished_position = self.finished_count

            if self._game_over():
                return {'ok': True, 'round_over': True}

            return {'ok': True, 'show_2': True}

        if not self.table_cards:
            for c in cards:
                player.remove_card(c)

            self.lead_player_idx = self.current_player_idx
            self.table_cards = cards
            self.table_meld_type = meld_type_str

            for p in self.players.values():
                p.passed = False

            if not player.has_cards():
                self.finished_count += 1
                player.finished_position = self.finished_count

            if self._game_over():
                return {'ok': True, 'round_over': True}

            self.next_player()
            return {'ok': True}

        is_valid, reason = compare_melds(cards, self.table_cards)
        if not is_valid:
            return {'ok': False, 'msg': f'Invalid play: {reason}'}

        for c in cards:
            player.remove_card(c)

        self.table_cards = cards
        self.table_meld_type = meld_type_str

        for p in self.players.values():
            p.passed = False

        if not player.has_cards():
            self.finished_count += 1
            player.finished_position = self.finished_count

        if self._game_over():
            return {'ok': True, 'round_over': True}

        self.next_player()
        return {'ok': True}

    def pass_turn(self, player_id):
        player = self.players.get(player_id)
        current = self.get_current_player()

        if not current or current.player_id != player_id:
            return {'ok': False, 'msg': 'Not your turn'}

        print(f"[PASS] {player.name} is passing")

        # BUG FIX: Check if player has finished
        if not player.has_cards() and player.finished_position is None:
            print(f"[PASS] {player.name} has no cards and finished")
            self.finished_count += 1
            player.finished_position = self.finished_count
            if self._game_over():
                return {'ok': True, 'round_over': True}

        players_with_cards = [p for p in self.players.values() if p.has_cards()]

        if len(players_with_cards) <= 1:
            print(f"[PASS] Only {len(players_with_cards)} player(s) with cards - ROUND OVER!")
            if not player.finished_position:
                self.finished_count += 1
                player.finished_position = self.finished_count
            return {'ok': True, 'round_over': True}

        player.passed = True
        active_players = [p for p in self.players.values() if p.has_cards()]
        not_passed = [p for p in active_players if not p.passed]

        print(f"[PASS] active_players: {len(active_players)}, not_passed: {len(not_passed)}")

        if len(not_passed) <= 1:
            print(f"[PASS] All passed - clearing table and resetting passes")
            self.table_cards = []
            self.table_meld_type = None
            self.lead_player_idx = 0
            for p in self.players.values():
                p.passed = False

        self.next_player()
        return {'ok': True}

    def _game_over(self):
        with_cards = sum(1 for p in self.players.values() if p.has_cards())
        result = with_cards <= 1
        print(f"[GAME_OVER] Checking: {with_cards} players with cards, game_over={result}")
        return result

    def _assign_roles(self):
        """BUG FIX: Complete role assignment dict for all player counts"""
        num_players = len(self.players)
        
        # FIX: Complete dict with proper closing bracket
        roles_by_position = {
            2: {1: 'President', 2: 'Asshole'},
            3: {1: 'President', 2: 'Citizen', 3: 'Asshole'},
            4: {1: 'President', 2: 'Vice President', 3: 'Vice Asshole', 4: 'Asshole'},
        }

        role_map = roles_by_position.get(num_players, {})

        finished = sorted(self.players.values(), key=lambda p: p.finished_position if p.finished_position else 999)

        print(f"[ROLES] Assigning roles. Finished order: {[p.name for p in finished]}")

        for i, player in enumerate(finished):
            position = i + 1
            role = role_map.get(position, 'Citizen')
            player.role = role
            print(f"[ROLES] {player.name}: position {position} -> {role}")

    def _deal_new_hands(self):
        deck = []
        for rank in Rank:
            for suit in Suit:
                deck.append(Card(rank, suit))
        random.shuffle(deck)

        for player in self.players.values():
            player.hand = []
            player.finished_position = None
            player.passed = False

        for i, card in enumerate(deck):
            idx = i % len(self.player_order)
            self.players[self.player_order[idx]].add_card(card)

        self.table_cards = []
        self.table_meld_type = None
        self.finished_count = 0
        self.cpu_playing = False
        self._showing_2 = False

    def _get_president(self):
        return next((p for p in self.players.values() if p.role == 'President'), None)

    def _get_asshole(self):
        return next((p for p in self.players.values() if p.role == 'Asshole'), None)

    def _get_vp(self):
        return next((p for p in self.players.values() if p.role == 'Vice President'), None)

    def _get_va(self):
        return next((p for p in self.players.values() if p.role == 'Vice Asshole'), None)

    def get_player_for_current_exchange(self):
        if self.exchange_state_enum == ExchangeState.WAITING_PRESIDENT:
            return self._get_president()
        elif self.exchange_state_enum == ExchangeState.WAITING_ASSHOLE:
            return self._get_asshole()
        elif self.exchange_state_enum == ExchangeState.WAITING_VP:
            return self._get_vp()
        elif self.exchange_state_enum == ExchangeState.WAITING_VA:
            return self._get_va()
        return None

    def get_exchange_state_str(self):
        mapping = {
            ExchangeState.WAITING_PRESIDENT: 'waiting_president',
            ExchangeState.WAITING_ASSHOLE: 'waiting_asshole',
            ExchangeState.WAITING_VP: 'waiting_vp',
            ExchangeState.WAITING_VA: 'waiting_va',
            ExchangeState.COMPLETE: 'complete',  # BUG FIX: Return 'complete' instead of None
        }
        return mapping.get(self.exchange_state_enum)

    def start_exchange_phase(self):
        print(f"\n{'='*70}")
        print(f"[EXCHANGE] ===== EXCHANGE PHASE STARTED =====")
        self._assign_roles()
        self._deal_new_hands()

        self.state = 'exchange'
        self.exchange_state_enum = ExchangeState.WAITING_PRESIDENT
        self.pending_exchanges = {}

        print(f"[EXCHANGE] President: {self._get_president().name}")
        print(f"[EXCHANGE] Asshole: {self._get_asshole().name}")
        print(f"{'='*70}\n")

    def complete_all_exchanges(self):
        print(f"\n{'='*70}")
        print(f"[COMPLETE-EX] START")
        print(f"{'='*70}")

        iteration = 0
        while iteration < 20:
            iteration += 1
            print(f"\n[EX-LOOP{iteration}] State: {self.exchange_state_enum}")

            current_player = self.get_player_for_current_exchange()

            if not current_player:
                print(f"[EX-LOOP{iteration}] ERROR: No player found!")
                break

            print(f"[EX-LOOP{iteration}] Player: {current_player.name} (CPU={current_player.is_cpu})")

            if self.exchange_state_enum == ExchangeState.COMPLETE:
                print(f"[EX-LOOP{iteration}] COMPLETE! Stopping.")
                break

            if not current_player.is_cpu:
                print(f"[EX-LOOP{iteration}] HUMAN - waiting for them")
                break

            print(f"[EX-LOOP{iteration}] FORCING {current_player.name} to submit...")
            success = self._force_cpu_exchange(current_player)

            if not success:
                print(f"[EX-LOOP{iteration}] ERROR: Force failed!")
                break

            print(f"[EX-LOOP{iteration}] Success! New state: {self.exchange_state_enum}")

        print(f"\n[COMPLETE-EX] END")
        print(f"[COMPLETE-EX] Final state: {self.exchange_state_enum}")
        print(f"[COMPLETE-EX] Final game.state: {self.state}")
        print(f"{'='*70}\n")

    def _force_cpu_exchange(self, player):
        if not player.is_cpu:
            print(f"[FORCE] ERROR: {player.name} is not CPU!")
            return False

        if self.exchange_state_enum == ExchangeState.WAITING_PRESIDENT:
            if player.role != 'President':
                print(f"[FORCE] ERROR: Expected President, got {player.role}")
                return False
            cards = player.hand[-2:] if len(player.hand) >= 2 else player.hand[:]

        elif self.exchange_state_enum == ExchangeState.WAITING_ASSHOLE:
            if player.role != 'Asshole':
                print(f"[FORCE] ERROR: Expected Asshole, got {player.role}")
                return False
            cards = player.hand[-2:] if len(player.hand) >= 2 else player.hand[:]

        elif self.exchange_state_enum == ExchangeState.WAITING_VP:
            if player.role != 'Vice President':
                print(f"[FORCE] ERROR: Expected VP, got {player.role}")
                return False
            cards = [player.hand[-1]] if player.hand else []

        elif self.exchange_state_enum == ExchangeState.WAITING_VA:
            if player.role != 'Vice Asshole':
                print(f"[FORCE] ERROR: Expected VA, got {player.role}")
                return False
            cards = [player.hand[-1]] if player.hand else []

        else:
            print(f"[FORCE] ERROR: Unknown state {self.exchange_state_enum}")
            return False

        if not cards:
            print(f"[FORCE] ERROR: No cards!")
            return False

        print(f"[FORCE] Submitting {len(cards)} cards")
        result = self._execute_exchange_submission(player, cards)

        if not result:
            print(f"[FORCE] ERROR: Submission failed")
            return False

        print(f"[FORCE] Success!")
        return True

    def _execute_exchange_submission(self, player, cards):
        print(f"[SUBMIT] {player.name} submit: {[str(c) for c in cards]}")

        try:
            if self.exchange_state_enum == ExchangeState.WAITING_PRESIDENT:
                asshole = self._get_asshole()
                if not asshole:
                    print(f"[SUBMIT] ERROR: Asshole not found!")
                    return False

                if asshole.is_cpu:
                    asshole_cards = asshole.hand[-2:] if len(asshole.hand) >= 2 else asshole.hand[:]
                    for c in cards:
                        player.remove_card(c)
                    asshole.add_card(c)
                    for c in asshole_cards:
                        asshole.remove_card(c)
                    player.add_card(c)

                    print(f"[SUBMIT] Exchanged: Pres <-> Ass")

                    vp = self._get_vp()
                    va = self._get_va()

                    if vp and va:
                        self.exchange_state_enum = ExchangeState.WAITING_VP
                        print(f"[SUBMIT] Moving to VP stage")
                    else:
                        self.exchange_state_enum = ExchangeState.COMPLETE
                        self.state = 'playing'
                        print(f"[SUBMIT] Exchange complete!")

                    return True
                else:
                    self.exchange_state_enum = ExchangeState.WAITING_ASSHOLE
                    print(f"[SUBMIT] Asshole is human, waiting")
                    return True

            elif self.exchange_state_enum == ExchangeState.WAITING_ASSHOLE:
                president = self._get_president()
                if not president:
                    print(f"[SUBMIT] ERROR: President not found!")
                    return False

                if president.is_cpu:
                    president_cards = president.hand[-2:] if len(president.hand) >= 2 else president.hand[:]
                    for c in cards:
                        player.remove_card(c)
                    president.add_card(c)
                    for c in president_cards:
                        president.remove_card(c)
                    player.add_card(c)

                    print(f"[SUBMIT] Exchanged: Ass <-> Pres")

                    vp = self._get_vp()
                    va = self._get_va()

                    if vp and va:
                        self.exchange_state_enum = ExchangeState.WAITING_VP
                        print(f"[SUBMIT] Moving to VP stage")
                    else:
                        self.exchange_state_enum = ExchangeState.COMPLETE
                        self.state = 'playing'
                        print(f"[SUBMIT] Exchange complete!")

                    return True
                else:
                    vp = self._get_vp()
                    va = self._get_va()
                    if vp and va:
                        self.exchange_state_enum = ExchangeState.WAITING_VP
                        print(f"[SUBMIT] Asshole submitted, moving to VP stage")
                    else:
                        self.exchange_state_enum = ExchangeState.COMPLETE
                        self.state = 'playing'
                        print(f"[SUBMIT] Exchange complete!")
                    return True

            elif self.exchange_state_enum == ExchangeState.WAITING_VP:
                va = self._get_va()
                if not va:
                    print(f"[SUBMIT] ERROR: VA not found!")
                    return False

                if va.is_cpu:
                    va_cards = [va.hand[-1]] if va.hand else []
                    for c in cards:
                        player.remove_card(c)
                    va.add_card(c)
                    for c in va_cards:
                        va.remove_card(c)
                    player.add_card(c)

                    print(f"[SUBMIT] Exchanged: VP <-> VA")

                    self.exchange_state_enum = ExchangeState.COMPLETE
                    self.state = 'playing'
                    print(f"[SUBMIT] Exchange complete!")
                    return True
                else:
                    self.exchange_state_enum = ExchangeState.WAITING_VA
                    print(f"[SUBMIT] VA is human, waiting")
                    return True

            elif self.exchange_state_enum == ExchangeState.WAITING_VA:
                vp = self._get_vp()
                if not vp:
                    print(f"[SUBMIT] ERROR: VP not found!")
                    return False

                if vp.is_cpu:
                    vp_cards = [vp.hand[-1]] if vp.hand else []
                    for c in cards:
                        player.remove_card(c)
                    vp.add_card(c)
                    for c in vp_cards:
                        vp.remove_card(c)
                    player.add_card(c)

                    print(f"[SUBMIT] Exchanged: VA <-> VP")

                    self.exchange_state_enum = ExchangeState.COMPLETE
                    self.state = 'playing'
                    print(f"[SUBMIT] Exchange complete!")
                    return True
                else:
                    self.exchange_state_enum = ExchangeState.COMPLETE
                    self.state = 'playing'
                    print(f"[SUBMIT] VA submitted, exchange complete!")
                    return True

            else:
                print(f"[SUBMIT] ERROR: Unsupported state {self.exchange_state_enum}")
                return False

        except Exception as e:
            print(f"[SUBMIT] EXCEPTION: {e}")
            traceback.print_exc()
            return False

    def human_submit_exchange(self, player_id, card_displays):
        player = self.players.get(player_id)
        if not player:
            return {'ok': False, 'msg': 'Player not found'}

        if self.state != 'exchange':
            return {'ok': False, 'msg': 'Not in exchange phase'}

        cards = []
        for display in card_displays:
            found = None
            for c in player.hand:
                if str(c) == display:
                    found = c
                    break
            if not found:
                return {'ok': False, 'msg': f'Card {display} not found'}
            cards.append(found)

        if not cards:
            return {'ok': False, 'msg': 'No cards selected'}

        if self.exchange_state_enum == ExchangeState.WAITING_PRESIDENT:
            if player.role != 'President':
                return {'ok': False, 'msg': 'Not your turn'}
            if len(cards) != 2:
                return {'ok': False, 'msg': 'President must give 2 cards'}

        elif self.exchange_state_enum == ExchangeState.WAITING_ASSHOLE:
            if player.role != 'Asshole':
                return {'ok': False, 'msg': 'Not your turn'}
            if len(cards) != 2:
                return {'ok': False, 'msg': 'Asshole must give 2 cards'}

        elif self.exchange_state_enum == ExchangeState.WAITING_VP:
            if player.role != 'Vice President':
                return {'ok': False, 'msg': 'Not your turn'}
            if len(cards) != 1:
                return {'ok': False, 'msg': 'VP must give 1 card'}

        elif self.exchange_state_enum == ExchangeState.WAITING_VA:
            if player.role != 'Vice Asshole':
                return {'ok': False, 'msg': 'Not your turn'}
            if len(cards) != 1:
                return {'ok': False, 'msg': 'VA must give 1 card'}

        else:
            return {'ok': False, 'msg': 'Invalid state'}

        result = self._execute_exchange_submission(player, cards)

        if not result:
            return {'ok': False, 'msg': 'Exchange failed'}

        return {'ok': True}

    def to_dict(self):
        return {
            'game_id': self.game_id,
            'players': [{
                'player_id': p.player_id,
                'name': p.name,
                'is_cpu': p.is_cpu,
                'hand': [str(card) for card in p.hand],
                'role': p.role,
                'finished_position': p.finished_position,
                'passed': p.passed,
            } for p in self.players.values()],
            'player_order': self.player_order,
            'original_player_order': self.original_player_order,
            'current_player_idx': self.current_player_idx,
            'lead_player_idx': self.lead_player_idx,
            'table_cards': [str(c) for c in self.table_cards],
            'table_meld_type': self.table_meld_type,
            'finished_count': self.finished_count,
            'state': self.state,
            'round_num': self.round_num,
            'exchange_state': self.get_exchange_state_str(),
            'pending_exchanges': {},
            'exchanges_complete': False,
        }

    @classmethod
    def from_dict(cls, data):
        game = cls(data['game_id'])
        game.players = {}

        for pdata in data['players']:
            p = Player(pdata['player_id'], pdata['name'], pdata['is_cpu'])
            p.hand = [Card.from_str(c) for c in pdata['hand']]
            p.role = pdata['role']
            p.finished_position = pdata['finished_position']
            p.passed = pdata['passed']
            game.players[p.player_id] = p

        game.player_order = data['player_order']
        game.original_player_order = data.get('original_player_order', [])
        game.current_player_idx = data['current_player_idx']
        game.cleanup_player_order()
        game.lead_player_idx = data['lead_player_idx']
        game.table_cards = [Card.from_str(c) for c in data['table_cards']]
        game.table_meld_type = data.get('table_meld_type')
        game.finished_count = data['finished_count']
        game.state = data['state']
        game.round_num = data['round_num']
        game.exchange_state_enum = None
        game.pending_exchanges = {}
        game.cpu_playing = False
        game._showing_2 = False

        return game

    def get_state(self):
        current = self.get_current_player()
        lead_player = None

        if self.lead_player_idx < len(self.player_order):
            lead_pid = self.player_order[self.lead_player_idx]
            lead_player = self.players.get(lead_pid)

        state = {
            'game_id': self.game_id,
            'state': self.state,
            'exchange_state': self.get_exchange_state_str(),
            'current_player': current.name if current else None,
            'current_is_cpu': current.is_cpu if current else False,
            'lead_player': lead_player.name if lead_player else None,
            'table': [str(c) for c in self.table_cards],
            'table_meld_type': self.table_meld_type,
            'round': self.round_num,
            'players': []
        }

        for p in self.players.values():
            pdata = {
                'id': p.player_id,
                'name': p.name,
                'role': p.role,
                'cards': len(p.hand),
                'is_cpu': p.is_cpu,
                'finished': p.finished_position,
                'hand': [str(c) for c in p.hand]
            }
            state['players'].append(pdata)

        return state

def save_game_to_disk(game):
    try:
        filename = f'{SAVE_DIR}/save_{game.game_id}.json'
        with open(filename, 'w') as f:
            json.dump(game.to_dict(), f, indent=2)
    except Exception as e:
        print(f"[SAVE ERROR] {e}")

def load_game_from_disk(game_id):
    try:
        filename = f'{SAVE_DIR}/save_{game_id}.json'
        if os.path.exists(filename):
            with open(filename, 'r') as f:
                data = json.load(f)
            return Game.from_dict(data)
    except Exception as e:
        print(f"[LOAD ERROR] {e}")
    return None

def get_valid_plays(player, table_meld_type, table_cards):
    """Generate all valid plays for CPU."""
    plays = []

    if not table_cards:
        all_ranks = set(c.rank for c in player.hand)
        for card in player.hand:
            plays.append([card])

        for rank in all_ranks:
            matching = [c for c in player.hand if c.rank == rank]
            if len(matching) >= 2:
                plays.append(matching[:2])

        for rank in all_ranks:
            matching = [c for c in player.hand if c.rank == rank]
            if len(matching) >= 3:
                plays.append(matching[:3])

        for rank in all_ranks:
            matching = [c for c in player.hand if c.rank == rank]
            if len(matching) >= 4:
                plays.append(matching[:4])

        sorted_cards = sorted(player.hand, key=lambda c: c.rank.value[0])
        for run_length in [3, 4, 5]:
            for i in range(len(sorted_cards) - run_length + 1):
                run = sorted_cards[i:i+run_length]
                is_run = all(run[j].rank.value[0] + 1 == run[j+1].rank.value[0]
                            for j in range(len(run)-1))
                if is_run:
                    plays.append(run)

    else:
        table_rank = table_cards[0].rank
        table_count = len(table_cards)

        if table_meld_type == "SINGLE":
            for card in player.hand:
                if card.rank.value[0] > table_rank.value[0]:
                    plays.append([card])

        elif table_meld_type == "PAIR":
            all_ranks = set(c.rank for c in player.hand)
            for rank in all_ranks:
                matching = [c for c in player.hand if c.rank == rank]
                if len(matching) >= 2:
                    meld = matching[:2]
                    if rank.value[0] > table_rank.value[0]:
                        plays.append(meld)

        elif table_meld_type == "TRIPLE":
            all_ranks = set(c.rank for c in player.hand)
            for rank in all_ranks:
                matching = [c for c in player.hand if c.rank == rank]
                if len(matching) >= 3:
                    meld = matching[:3]
                    if rank.value[0] > table_rank.value[0]:
                        plays.append(meld)

        elif table_meld_type == "QUAD":
            all_ranks = set(c.rank for c in player.hand)
            for rank in all_ranks:
                matching = [c for c in player.hand if c.rank == rank]
                if len(matching) >= 4:
                    meld = matching[:4]
                    if rank.value[0] > table_rank.value[0]:
                        plays.append(meld)

        elif table_meld_type and table_meld_type.startswith("RUN"):
            sorted_cards = sorted(player.hand, key=lambda c: c.rank.value[0])
            for i in range(len(sorted_cards) - table_count + 1):
                run = sorted_cards[i:i+table_count]
                is_run = all(run[j].rank.value[0] + 1 == run[j+1].rank.value[0]
                            for j in range(len(run)-1))
                if is_run:
                    run_min = min(c.rank.value[0] for c in run)
                    table_min = min(c.rank.value[0] for c in table_cards)
                    if run_min > table_min:
                        plays.append(run)

    return plays

@app.route('/')
def index():
    return render_template('president.html')

@socketio.on('connect')
def on_connect():
    pass

@socketio.on('create')
def on_create(data):
    name = data.get('name', 'Player')
    cpus = data.get('cpus', 2)
    custom_table_id = data.get('table_id', None)

    if custom_table_id and custom_table_id.strip():
        gid = custom_table_id.strip().lower()
    else:
        gid = secrets.token_hex(4)

    existing_game = load_game_from_disk(gid)

    if existing_game:
        game = existing_game
        existing_player_id, existing_player = game.find_player_by_name(name)

        if existing_player_id:
            print(f"[CREATE] Player {name} rejoining")
            game.rejoin_player(existing_player_id, request.sid, name)
        else:
            cpu_players = [pid for pid, p in game.players.items() if p.is_cpu]
            if cpu_players:
                cpu_id = cpu_players[0]
                print(f"[CREATE] Replacing CPU {cpu_id} with player {name}")
                del game.players[cpu_id]
                if cpu_id in game.player_order:
                    idx = game.player_order.index(cpu_id)
                    game.player_order[idx] = request.sid
                if cpu_id in game.original_player_order:
                    idx = game.original_player_order.index(cpu_id)
                    game.original_player_order[idx] = request.sid
                game.add_player(request.sid, name, is_cpu=False)
            else:
                emit('error', {'msg': 'Game is full'})
                return
    else:
        game = Game(gid)
        game.add_player(request.sid, name, is_cpu=False)
        for i in range(cpus):
            cpu_id = f'cpu_{i}_{secrets.token_hex(2)}'
            game.add_player(cpu_id, f'CPU-{i+1}', is_cpu=True)

    if game.can_start():
        game.start_round()

    games[gid] = game
    join_room(gid)
    session['game_id'] = gid

    save_game_to_disk(game)

    state = game.get_state()
    emit('created', {'game_id': gid, 'state': state})
    socketio.emit('update', {'state': state}, to=gid, skip_sid=request.sid)

    current = game.get_current_player()
    if current and current.is_cpu:
        socketio.emit('cpu_turn', {}, to=gid)

@socketio.on('play')
def on_play(data):
    gid = session.get('game_id')
    if gid not in games:
        emit('error', {'msg': 'Game not found'})
        return

    game = games[gid]

    if hasattr(game, '_showing_2') and game._showing_2:
        emit('error', {'msg': 'Wait, 2 is being cleared...'})
        return

    result = game.play_cards(request.sid, data.get('cards', []))

    if not result['ok']:
        emit('error', {'msg': result['msg']})
        return

    if result.get('round_over'):
        print(f"[PLAY] Round over - starting exchange phase")
        game.start_exchange_phase()
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        print(f"[PLAY] Completing exchanges...")
        game.complete_all_exchanges()
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        if game.state == 'playing':
            print(f"[PLAY] Exchanges complete, resuming game")
            game.start_round(preserve_roles=True)
            save_game_to_disk(game)
            socketio.emit('update', {'state': game.get_state()}, to=gid)

            current = game.get_current_player()
            if current and current.is_cpu:
                socketio.emit('cpu_turn', {}, to=gid)

        return

    if result.get('show_2'):
        game._showing_2 = True
        socketio.emit('update', {'state': game.get_state()}, to=gid)
        time.sleep(1.0)

        game.table_cards = []
        game.table_meld_type = None
        for p in game.players.values():
            p.passed = False

        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)
        game._showing_2 = False

        current = game.get_current_player()
        if current and current.is_cpu:
            socketio.emit('cpu_turn', {}, to=gid)
    else:
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        current = game.get_current_player()
        if current and current.is_cpu:
            socketio.emit('cpu_turn', {}, to=gid)

@socketio.on('pass')
def on_pass():
    gid = session.get('game_id')
    if gid not in games:
        emit('error', {'msg': 'Game not found'})
        return

    game = games[gid]

    if hasattr(game, '_showing_2') and game._showing_2:
        emit('error', {'msg': 'Wait, 2 is being cleared...'})
        return

    result = game.pass_turn(request.sid)

    if not result['ok']:
        emit('error', {'msg': result['msg']})
        return

    save_game_to_disk(game)
    socketio.emit('update', {'state': game.get_state()}, to=gid)

    if result.get('round_over'):
        print(f"[PASS] Round over - starting exchange phase")
        game.start_exchange_phase()
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        print(f"[PASS] Completing exchanges...")
        game.complete_all_exchanges()
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        if game.state == 'playing':
            print(f"[PASS] Exchanges complete, resuming game")
            game.start_round(preserve_roles=True)
            save_game_to_disk(game)
            socketio.emit('update', {'state': game.get_state()}, to=gid)

            current = game.get_current_player()
            if current and current.is_cpu:
                socketio.emit('cpu_turn', {}, to=gid)

        return

    current = game.get_current_player()
    if current and current.is_cpu:
        socketio.emit('cpu_turn', {}, to=gid)

@socketio.on('submit_exchange')
def on_submit_exchange(data):
    gid = session.get('game_id')
    if gid not in games:
        emit('error', {'msg': 'Game not found'})
        return

    game = games[gid]

    result = game.human_submit_exchange(request.sid, data.get('cards', []))

    if not result['ok']:
        emit('error', {'msg': result['msg']})
        return

    save_game_to_disk(game)

    game.complete_all_exchanges()

    save_game_to_disk(game)
    socketio.emit('update', {'state': game.get_state()}, to=gid)

    if game.state == 'playing':
        game.start_round(preserve_roles=True)
        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        current = game.get_current_player()
        if current and current.is_cpu:
            socketio.emit('cpu_turn', {}, to=gid)

@socketio.on('cpu_play')
def on_cpu_play():
    gid = session.get('game_id')
    if gid not in games:
        return

    game = games[gid]

    if game.cpu_playing:
        return

    game.cpu_playing = True

    try:
        if game.state != 'playing':
            return

        current = game.get_current_player()
        if not current or not current.is_cpu or not current.has_cards():
            return

        time.sleep(0.8)

        plays = get_valid_plays(current, game.table_meld_type, game.table_cards)

        if not plays:
            result = game.pass_turn(current.player_id)
        else:
            result = game.play_cards(current.player_id, [str(c) for c in plays[0]])

        # ✅ CHECK FOR round_over!
        if result.get('round_over'):
            print(f"[CPU_PLAY] Round over - starting exchange phase")
            game.start_exchange_phase()
            save_game_to_disk(game)
            socketio.emit('update', {'state': game.get_state()}, to=gid)

            print(f"[CPU_PLAY] Completing exchanges...")
            game.complete_all_exchanges()
            save_game_to_disk(game)
            socketio.emit('update', {'state': game.get_state()}, to=gid)

            if game.state == 'playing':
                print(f"[CPU_PLAY] Exchanges complete, resuming game")
                game.start_round(preserve_roles=True)
                save_game_to_disk(game)
                socketio.emit('update', {'state': game.get_state()}, to=gid)

                current = game.get_current_player()
                if current and current.is_cpu:
                    socketio.emit('cpu_turn', {}, to=gid)

            return

        save_game_to_disk(game)
        socketio.emit('update', {'state': game.get_state()}, to=gid)

        if game.state == 'playing':
            current = game.get_current_player()
            if current and current.is_cpu:
                socketio.emit('cpu_turn', {}, to=gid)

    finally:
        game.cpu_playing = False

if __name__ == '__main__':
 port = int(os.environ.get('PORT', 5000))
socketio.run(app, debug=False, host='0.0.0.0', port=port)