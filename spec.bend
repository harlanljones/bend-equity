# spec.bend: the data model and the definitions the laws are stated in.
# Human-owned: agents never edit this file.
import Base
import ./comb.bend as Comb

# A card is a Nat 0..51: rank = c / 4 (0 = '2' .. 12 = 'A'), suit = c % 4 (0 c, 1 d, 2 h, 3 s).
type Hand is Data:
  Hand{x: Nat, y: Nat}

# The players' hands in seat order, and the board cards already dealt (0, 3, 4 or 5).
type Spot is Data:
  Spot{hands: List<&2, Hand>, board: List<&2, Nat>}

# One player's result over every board; share is in units of 1/2520 pot per board (2520 = lcm(1..10)).
type Tally is Data:
  Tally{win: Nat, tie: Nat, lose: Nat, share: Nat}

def not_(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

def has(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Nat.is_eq(h, c) || has(t, c)

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len(t)

def ascending_from(xs: List<&2, Nat>, +prev: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Nat.is_lt(prev, h) && ascending_from(t, h)

def ascending(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      ascending_from(t, h)

def all_lt(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Nat.is_lt(h, n) && all_lt(t, n)

def distinct(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      not_(has(t, h)) && distinct(t)

# Strictly ascending (no card twice) and only real cards.
def well_formed(+b: List<&2, Nat>) -> Bool:
  ascending(b) && all_lt(b, 52n)

def count(hs: List<&2, Hand>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count(t)

# Every known card: the hole cards in seat order, then the board.
def cards(hs: List<&2, Hand>, b: List<&2, Nat>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      b
    case Con{Hand{x, y}, t}:
      x <> y <> cards(t, b)

def board_size_ok(+m: Nat) -> Bool:
  Nat.is_eq(m, 0n) || Nat.is_eq(m, 3n) || Nat.is_eq(m, 4n) || Nat.is_eq(m, 5n)

# The spots the engine promises to handle: 2..10 players, a 0/3/4/5-card board, real cards, no card twice.
def valid(s: Spot) -> Bool:
  match s:
    case Spot{+hs, +b}:
      +n = count(hs)
      +all = cards(hs, b)
      Nat.is_le(2n, n) && Nat.is_le(n, 10n) && board_size_ok(len(b)) && all_lt(all, 52n) && distinct(all)

def players(s: Spot) -> Nat:
  match s:
    case Spot{hs, b}:
      count(hs)

# How many boards complete the spot: C(52 - known cards, 5 - board cards).
def boards(s: Spot) -> Nat:
  match s:
    case Spot{+hs, +b}:
      Comb.binom(Nat.sub(52n, len(cards(hs, b))), Nat.sub(5n, len(b)))

def tcount(ts: List<&2, Tally>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{t, rest}:
      1n+tcount(rest)

def all_sum(ts: List<&2, Tally>, +n: Nat) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{Tally{w, t, l, _}, rest}:
      Nat.is_eq(Nat.add(w, Nat.add(t, l)), n) && all_sum(rest, n)

# Exactly one tally per player, each counting every board exactly once.
def counted(+ts: List<&2, Tally>, +m: Nat, +n: Nat) -> Bool:
  Nat.is_eq(tcount(ts), m) && all_sum(ts, n)

def share_sum(ts: List<&2, Tally>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{Tally{_, _, _, s}, rest}:
      Nat.add(s, share_sum(rest))

def swap2(ts: List<&2, Tally>) -> List<&2, Tally>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{a, Nil{}}:
      [a]
    case Con{a, Con{b, Nil{}}}:
      [b, a]
    case Con{a, Con{b, Con{c, r}}}:
      a <> b <> c <> r

def heads_up(+p: Hand, +q: Hand, b: List<&2, Nat>) -> Spot:
  Spot{[p, q], b}
