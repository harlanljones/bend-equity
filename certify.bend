# certify.bend: the evaluator over all C(52, 7) = 133784560 seven-card hands,
# as a histogram of categories, beside the known counts.
import Base
import ./comb.bend as Comb
import ./eval.bend as Eval

# The hands certified, all of C(52, 7).
def hands() -> Nat:
  133784560n

def zeros(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> zeros(p)

# n slots, 1 at index c.
def onehot(n: Nat, c: Nat) -> List<&2, Nat>:
  match n c:
    case 0n _:
      Nil{}
    case 1n+p 0n:
      1n <> zeros(p)
    case 1n+p 1n+q:
      0n <> onehot(p, q)

# Padded add: Nil is the empty histogram.
def nadd(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a b:
    case Nil{} _:
      b
    case Con{x, xs} Nil{}:
      x <> xs
    case Con{x, xs} Con{y, ys}:
      Nat.add(x, y) <> nadd(xs, ys)

def hist_of(cs: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Con{+x, Con{+y, rest}}:
      onehot(9n, Eval.category(Eval.score7(x, y, rest)))
    case _:
      Nil{}

def hist_at.go(ok: Bool, dk: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match ok:
    case True{}:
      hist_of(Comb.board(dk, 52n, 7n, i))
    case False{}:
      Nil{}

# Hand i as a one-hot histogram of its category, Nil past the last hand.
def hist_at(+dk: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  hist_at.go(Nat.is_lt(i, hands()), dk, i)

def seq(m: Nat, +dk: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match m:
    case 0n:
      Nil{}
    case 1n++p:
      nadd(seq(p, dk, i), hist_at(dk, Nat.add(p, i)))

# A private copy of the deck: a leaf that reads its own copy pays no atomic
# count on a list every lane shares.
def copy(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

def tree(d: Nat, +c: Nat, +dk: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match d:
    case 0n:
      seq(Comb.pow2(c), copy(dk), i)
    case 1n++p:
      l r = tree(p, c, dk, i) tree(p, c, dk, Nat.add(Comb.pow2(Nat.add(p, c)), i))
      nadd(l, r)

# 2^27 >= C(52, 7): 2^14 leaves of 2^13 hands, on the GPU.
def hist() -> List<&2, Nat>:
  tree!(14n, 13n, Comb.deck(Nil{}), 0n)

# The known counts, 0 high card .. 8 straight flush.
def expected() -> List<&2, Nat>:
  [23294460n, 58627800n, 31433400n, 6461620n, 6180020n, 4047644n, 3473184n, 224848n, 41584n]
