# eval.bend: the 7-card evaluator. Four 13-bit suit masks (bit r = rank r)
# give every category by bit arithmetic; the score is
# cat << 26 | hi << 13 | lo, so a larger score is a better hand.
import Base

type Masks is Data:
  Masks{c: U32, d: U32, h: U32, s: U32}

def b2u(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# The number of set bits of a 13-bit mask: each round clears the lowest.
def popcount.go(f: Nat, +m: U32, acc: U32) -> U32:
  match f:
    case 0n:
      acc
    case 1n+g:
      popcount.go(g, (m .&. (m - 1) : U32), (acc + b2u(U32.is_ne(m, 0)) : U32))

def popcount(+m: U32) -> U32:
  popcount.go(13n, m, 0)

# Clears the n lowest set bits (n <= 13).
def drop_low(n: Nat, +m: U32) -> U32:
  match n:
    case 0n:
      m
    case 1n+p:
      drop_low(p, (m .&. (m - 1) : U32))

# The k highest set bits.
def topk(+m: U32, k: Nat) -> U32:
  drop_low(Nat.sub(U32.to_nat(popcount(m)), k), m)

# The highest set bit (m != 0).
def top1(m: U32) -> U32:
  (1 << U32.log2(m) : U32)

# Bit j set iff ranks j-1 .. j+3 are all held (bit 0 is the ace, low): 0 is
# A-2-3-4-5, 9 is T-J-Q-K-A. Zero when there is no straight.
def straight(+m: U32) -> U32:
  +a = ((m << 1n) .|. ((m >> 12n) .&. 1) : U32)
  (a .&. (a >> 1n) .&. (a >> 2n) .&. (a >> 3n) .&. (a >> 4n) : U32)

# A suit mask if it holds five cards or more, else 0.
def flush1(+m: U32) -> U32:
  (m * b2u(U32.is_ge(popcount(m), 5)) : U32)

# The categories, lowest first: each takes its own test as `hit` and, on a
# miss, tests and calls the one below it.
def s_high(+any: U32) -> U32:
  topk(any, 5n)

def s_pair(+any: U32, +p2: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((1 << 26n) .|. (p2 << 13n) .|. topk((any .&. U32.not(p2) : U32), 3n) : U32)
    case False{}:
      s_high(any)

def s_two(+any: U32, +p2: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      +tp = topk(p2, 2n)
      ((2 << 26n) .|. (tp << 13n) .|. top1((any .&. U32.not(tp) : U32)) : U32)
    case False{}:
      s_pair(any, p2, U32.is_ne(p2, 0))

def s_trips(+any: U32, +p2: U32, +p3: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((3 << 26n) .|. (p3 << 13n) .|. topk((any .&. U32.not(p3) : U32), 2n) : U32)
    case False{}:
      s_two(any, p2, U32.is_ge(popcount(p2), 2))

def s_straight(+any: U32, +p2: U32, +p3: U32, run: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((4 << 26n) .|. U32.from_nat(U32.log2(run)) : U32)
    case False{}:
      s_trips(any, p2, p3, U32.is_ne(p3, 0))

def s_flush(+any: U32, +p2: U32, +p3: U32, +f: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((5 << 26n) .|. topk(f, 5n) : U32)
    case False{}:
      +run = straight(any)
      s_straight(any, p2, p3, run, U32.is_ne(run, 0))

def s_full(+any: U32, +p2: U32, +p3: U32, +f: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      +t3 = top1(p3)
      ((6 << 26n) .|. (t3 << 13n) .|. top1((p2 .&. U32.not(t3) : U32)) : U32)
    case False{}:
      s_flush(any, p2, p3, f, U32.is_ne(f, 0))

def s_quads(+any: U32, +p2: U32, +p3: U32, +p4: U32, +f: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((7 << 26n) .|. (p4 << 13n) .|. top1((any .&. U32.not(p4) : U32)) : U32)
    case False{}:
      +rest = (p2 .&. U32.not(top1(p3)) : U32)
      s_full(any, p2, p3, f, U32.is_ne(p3, 0) && U32.is_ne(rest, 0))

def s_sflush(+any: U32, +p2: U32, +p3: U32, +p4: U32, +f: U32, run: U32, hit: Bool) -> U32:
  match hit:
    case True{}:
      ((8 << 26n) .|. U32.from_nat(U32.log2(run)) : U32)
    case False{}:
      s_quads(any, p2, p3, p4, f, U32.is_ne(p4, 0))

def classify(m: Masks) -> U32:
  match m:
    case Masks{+c, +d, +h, +s}:
      +any = (c .|. d .|. h .|. s : U32)
      +p2 = ((c .&. d) .|. (c .&. h) .|. (c .&. s) .|. (d .&. h) .|. (d .&. s) .|. (h .&. s) : U32)
      +p3 = ((c .&. d .&. h) .|. (c .&. d .&. s) .|. (c .&. h .&. s) .|. (d .&. h .&. s) : U32)
      +p4 = (c .&. d .&. h .&. s : U32)
      +f = (flush1(c) .|. flush1(d) .|. flush1(h) .|. flush1(s) : U32)
      +run = straight(f)
      s_sflush(any, p2, p3, p4, f, run, U32.is_ne(run, 0))

# Sets bit `b` in the mask of the given suit (0 c, 1 d, 2 h, 3 s).
def put(suit: Nat, b: U32, m: Masks) -> Masks:
  match suit m:
    case 0n Masks{c, d, h, s}:
      Masks{(c .|. b : U32), d, h, s}
    case 1n Masks{c, d, h, s}:
      Masks{c, (d .|. b : U32), h, s}
    case 2n Masks{c, d, h, s}:
      Masks{c, d, (h .|. b : U32), s}
    case _ Masks{c, d, h, s}:
      Masks{c, d, h, (s .|. b : U32)}

def add(+c: Nat, m: Masks) -> Masks:
  put(Nat.mod(c, 4n), (1 << Nat.div(c, 4n) : U32), m)

def masks(xs: List<&2, Nat>, m: Masks) -> Masks:
  match xs:
    case Nil{}:
      m
    case Con{h, t}:
      masks(t, add(h, m))

# The score of hole cards x, y with the five cards of b.
def score7(+x: Nat, +y: Nat, b: List<&2, Nat>) -> Nat:
  U32.to_nat(classify(masks(b, add(y, add(x, Masks{0, 0, 0, 0})))))

# The category of a score: 0 high card .. 8 straight flush.
def category(+s: Nat) -> Nat:
  Nat.div(s, 67108864n)
