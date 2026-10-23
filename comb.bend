# comb.bend: the combinatorics. A card is a Nat 0..51; a deck is the
# ascending list of cards not yet known; a board is the i-th k-subset of a
# deck in lexicographic order.
import Base

def pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n+p:
      +h = pow2(p)
      Nat.add(h, h)

def clog2.if(+d: Nat, rest: Unit -> Nat, ok: Bool) -> Nat:
  match ok:
    case True{}:
      d
    case False{}:
      rest(Unit{})

# Counts d up from 0 until pow2(d) >= n. The fuel is n itself: pow2(n) >= n,
# so the search always stops on its test, and the bound needs no constant.
def clog2.go(fuel: Nat, +n: Nat, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      clog2.if(d, u => clog2.go(f, n, 1n+d), Nat.is_le(n, pow2(d)))

# The smallest d with pow2(d) >= n (0 for n = 0 and n = 1).
def clog2(+n: Nat) -> Nat:
  clog2.go(n, n, 0n)

# C(n, k), exact at every step: (m+1) * C(m, j) is divisible by j+1.
def binom(n: Nat, k: Nat) -> Nat:
  match n k:
    case _ 0n:
      1n
    case 0n 1n+j:
      0n
    case 1n++m 1n++j:
      Nat.div(Nat.mul(1n+m, binom(m, j)), 1n+j)

def mem(xs: List<&2, Nat>, +c: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Nat.is_eq(h, c) || mem(t, c)

def deck.put(known: Bool, c: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match known:
    case True{}:
      acc
    case False{}:
      c <> acc

# The cards below n that are not known, ascending, consed onto acc.
def deck.go(n: Nat, +known: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n++p:
      deck.go(p, known, deck.put(mem(known, p), p, acc))

def deck(known: List<&2, Nat>) -> List<&2, Nat>:
  deck.go(52n, known, Nil{})

def deck_size.one(known: Bool) -> Nat:
  match known:
    case True{}:
      0n
    case False{}:
      1n

# How many cards below n are not known.
def deck_size.go(n: Nat, +known: List<&2, Nat>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n++p:
      Nat.add(deck_size.one(mem(known, p)), deck_size.go(p, known))

def deck_size(known: List<&2, Nat>) -> Nat:
  deck_size.go(52n, known)

def board.pick(take: Bool, a: Nat, b: Nat) -> Nat:
  match take:
    case True{}:
      a
    case False{}:
      b

def board.put(take: Bool, h: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match take:
    case True{}:
      h <> rest
    case False{}:
      rest

# The i-th k-subset of deck (n = its length) in lexicographic order: the
# C(m, j) subsets that take the head come first, then those that skip it.
def board(deck: List<&2, Nat>, n: Nat, k: Nat, +i: Nat) -> List<&2, Nat>:
  match deck n k:
    case Nil{} _ _:
      Nil{}
    case Con{h, t} 0n _:
      Nil{}
    case Con{h, t} 1n+m 0n:
      Nil{}
    case Con{h, t} 1n++m 1n++j:
      +b = binom(m, j)
      +take = Nat.is_lt(i, b)
      board.put(take, h, board(t, m, board.pick(take, j, 1n+j), board.pick(take, i, Nat.sub(i, b))))
