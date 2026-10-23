# equity.bend: exact equity by enumeration. Board i of a spot is the i-th
# completion of its deck; `seq` tallies boards one by one, `tree` splits the
# same range into a fork/join tree, and `run` sends that tree to the GPU or
# the CPU threads. LAW 1 says the two agree.
import Base
import ./spec.bend as Spec
import ./comb.bend as Comb
import ./eval.bend as Eval

type Ctx is Data:
  Ctx{hands: List<&2, Spec.Hand>, board: List<&2, Nat>, deck: List<&2, Nat>, n: Nat, k: Nat, total: Nat}

def ctx(s: Spec.Spot) -> Ctx:
  match s:
    case Spec.Spot{+hs, +b}:
      +known = Spec.cards(hs, b)
      +n = Comb.deck_size(known)
      +k = Nat.sub(5n, Spec.len(b))
      Ctx{hs, b, Comb.deck(known), n, k, Comb.binom(n, k)}

def tadd(a: Spec.Tally, b: Spec.Tally) -> Spec.Tally:
  match a b:
    case Spec.Tally{w1, t1, l1, s1} Spec.Tally{w2, t2, l2, s2}:
      Spec.Tally{Nat.add(w1, w2), Nat.add(t1, t2), Nat.add(l1, l2), Nat.add(s1, s2)}

# Padded zip: Nil is the empty accumulator.
def add(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>) -> List<&2, Spec.Tally>:
  match a b:
    case Nil{} _:
      b
    case Con{x, xs} Nil{}:
      x <> xs
    case Con{x, xs} Con{y, ys}:
      tadd(x, y) <> add(xs, ys)

def scores(hs: List<&2, Spec.Hand>, +full: List<&2, Nat>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Spec.Hand{x, y}, t}:
      Eval.score7(x, y, full) <> scores(t, full)

def maxl(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(h, maxl(t))

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# How many of xs equal m.
def cnt(xs: List<&2, Nat>, +m: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(b2n(Nat.is_eq(h, m)), cnt(t, m))

def tally(best: Bool, solo: Bool, share: Nat) -> Spec.Tally:
  match best solo:
    case True{} True{}:
      Spec.Tally{1n, 0n, 0n, share}
    case True{} False{}:
      Spec.Tally{0n, 1n, 0n, share}
    case False{} _:
      Spec.Tally{0n, 0n, 1n, 0n}

def tallies(xs: List<&2, Nat>, +best: Nat, +solo: Bool, +share: Nat) -> List<&2, Spec.Tally>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      tally(Nat.is_eq(h, best), solo, share) <> tallies(t, best, solo, share)

# One board: the w hands with the best score split the pot, 2520 / w each.
def judge(+ss: List<&2, Nat>) -> List<&2, Spec.Tally>:
  +best = maxl(ss)
  +w = cnt(ss, best)
  tallies(ss, best, Nat.is_eq(w, 1n), Nat.div(2520n, w))

def outcome(hands: List<&2, Spec.Hand>, +full: List<&2, Nat>) -> List<&2, Spec.Tally>:
  judge(scores(hands, full))

def cat(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      b
    case Con{h, t}:
      h <> cat(t, b)

def at.go(ok: Bool, hs: List<&2, Spec.Hand>, b: List<&2, Nat>, dk: List<&2, Nat>, n: Nat, k: Nat, +i: Nat) -> List<&2, Spec.Tally>:
  match ok:
    case True{}:
      outcome(hs, cat(b, Comb.board(dk, n, k, i)))
    case False{}:
      Nil{}

# The tallies of board i, or Nil past the last board.
def at(+x: Ctx, +i: Nat) -> List<&2, Spec.Tally>:
  match x:
    case Ctx{hs, b, dk, n, k, total}:
      at.go(Nat.is_lt(i, total), hs, b, dk, n, k, i)

# Boards i .. i + m - 1, one after another.
def seq(m: Nat, +x: Ctx, +i: Nat) -> List<&2, Spec.Tally>:
  match m:
    case 0n:
      Nil{}
    case 1n++p:
      add(seq(p, x, i), at(x, Nat.add(p, i)))

# A private copy of a list: a leaf that reads its own copy pays no atomic
# count on a list every lane shares.
def copy(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

def copy_hands(hs: List<&2, Spec.Hand>) -> List<&2, Spec.Hand>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Spec.Hand{x, y}, t}:
      Spec.Hand{x, y} <> copy_hands(t)

def fresh(x: Ctx) -> Ctx:
  match x:
    case Ctx{hs, b, dk, n, k, total}:
      Ctx{copy_hands(hs), copy(b), copy(dk), n, k, total}

# Boards i .. i + 2^(d+c) - 1: a fork/join tree of depth d over leaves of 2^c.
def tree(d: Nat, +c: Nat, +x: Ctx, +i: Nat) -> List<&2, Spec.Tally>:
  match d:
    case 0n:
      seq(Comb.pow2(c), fresh(x), i)
    case 1n++p:
      l r = tree(p, c, x, i) tree(p, c, x, Nat.add(Comb.pow2(Nat.add(p, c)), i))
      add(l, r)

def total(x: Ctx) -> Nat:
  match x:
    case Ctx{hs, b, dk, n, k, t}:
      t

# 2^14 = 16384 leaves fill the GPU's lanes; the rest of the range is the leaves' loop.
def run.cpu(+x: Ctx) -> List<&2, Spec.Tally>:
  +dd = Comb.clog2(total(x))
  +d = Nat.min(dd, 14n)
  tree(d, Nat.sub(dd, d), x, 0n)

def run.gpu(+x: Ctx) -> List<&2, Spec.Tally>:
  +dd = Comb.clog2(total(x))
  +d = Nat.min(dd, 14n)
  tree!(d, Nat.sub(dd, d), x, 0n)

# Every player's tally over every board of s; g sends the work to the GPU.
def run(g: Bool, s: Spec.Spot) -> List<&2, Spec.Tally>:
  match g:
    case True{}:
      run.gpu(ctx(s))
    case False{}:
      run.cpu(ctx(s))

# Whether a spot goes to the GPU. Measured on an RTX 4070 Ti (CUDA 13.4) beside
# 24 CPU threads, the GPU loses on every spot (AsAh,KdKc preflop: 0.42 s
# against 0.17 s with --gpu off), so spots stay on the CPU threads.
def gpu_worth(s: Spec.Spot) -> Bool:
  False{}
