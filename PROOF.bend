import Base
import ./spec.bend as Spec
import ./comb.bend as Comb
import ./equity.bend as Eq
import ./LAWS.bend as Laws

# Nat
# ===

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# Tallies
# =======

def tadd_assoc(a: Spec.Tally, b: Spec.Tally, c: Spec.Tally) -> {Eq.tadd(a, Eq.tadd(b, c)) == Eq.tadd(Eq.tadd(a, b), c) : Spec.Tally}:
  match a b c:
    case Spec.Tally{w1, t1, l1, s1} Spec.Tally{w2, t2, l2, s2} Spec.Tally{w3, t3, l3, s3}:
      %add_assoc(w1, w2, w3) : {Eq.tadd(Spec.Tally{w1, t1, l1, s1}, Eq.tadd(Spec.Tally{w2, t2, l2, s2}, Spec.Tally{w3, t3, l3, s3})) == Spec.Tally{_, Nat.add(Nat.add(t1, t2), t3), Nat.add(Nat.add(l1, l2), l3), Nat.add(Nat.add(s1, s2), s3)} : Spec.Tally}
      %add_assoc(t1, t2, t3) : {Eq.tadd(Spec.Tally{w1, t1, l1, s1}, Eq.tadd(Spec.Tally{w2, t2, l2, s2}, Spec.Tally{w3, t3, l3, s3})) == Spec.Tally{Nat.add(w1, Nat.add(w2, w3)), _, Nat.add(Nat.add(l1, l2), l3), Nat.add(Nat.add(s1, s2), s3)} : Spec.Tally}
      %add_assoc(l1, l2, l3) : {Eq.tadd(Spec.Tally{w1, t1, l1, s1}, Eq.tadd(Spec.Tally{w2, t2, l2, s2}, Spec.Tally{w3, t3, l3, s3})) == Spec.Tally{Nat.add(w1, Nat.add(w2, w3)), Nat.add(t1, Nat.add(t2, t3)), _, Nat.add(Nat.add(s1, s2), s3)} : Spec.Tally}
      %add_assoc(s1, s2, s3) : {Eq.tadd(Spec.Tally{w1, t1, l1, s1}, Eq.tadd(Spec.Tally{w2, t2, l2, s2}, Spec.Tally{w3, t3, l3, s3})) == Spec.Tally{Nat.add(w1, Nat.add(w2, w3)), Nat.add(t1, Nat.add(t2, t3)), Nat.add(l1, Nat.add(l2, l3)), _} : Spec.Tally}
      {==}

def add_nil(a: List<&2, Spec.Tally>) -> {Eq.add(a, Nil{}) == a : List<&2, Spec.Tally>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      {==}

def ladd_assoc(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>, c: List<&2, Spec.Tally>) -> {Eq.add(a, Eq.add(b, c)) == Eq.add(Eq.add(a, b), c) : List<&2, Spec.Tally>}:
  match a b c:
    case Nil{} _ _:
      {==}
    case Con{x, xs} Nil{} _:
      {==}
    case Con{x, xs} Con{y, ys} Nil{}:
      {==}
    case Con{+x, xs} Con{+y, ys} Con{+z, zs}:
      %ladd_assoc(xs, ys, zs) : {Eq.add(Con{x, xs}, Eq.add(Con{y, ys}, Con{z, zs})) == Con{Eq.tadd(Eq.tadd(x, y), z), _} : List<&2, Spec.Tally>}
      %tadd_assoc(x, y, z) : {Eq.add(Con{x, xs}, Eq.add(Con{y, ys}, Con{z, zs})) == Con{_, Eq.add(xs, Eq.add(ys, zs))} : List<&2, Spec.Tally>}
      {==}

# LAW 1
# =====

def copy_id(xs: List<&2, Nat>) -> {Eq.copy(xs) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %copy_id(t) : {Eq.copy(Con{h, t}) == Con{h, _} : List<&2, Nat>}
      {==}

def copy_hands_id(hs: List<&2, Spec.Hand>) -> {Eq.copy_hands(hs) == hs : List<&2, Spec.Hand>}:
  match hs:
    case Nil{}:
      {==}
    case Con{Spec.Hand{x, y}, t}:
      %copy_hands_id(t) : {Eq.copy_hands(Con{Spec.Hand{x, y}, t}) == Con{Spec.Hand{x, y}, _} : List<&2, Spec.Hand>}
      {==}

def fresh_id(x: Eq.Ctx) -> {Eq.fresh(x) == x : Eq.Ctx}:
  match x:
    case Eq.Ctx{hs, b, dk, n, k, t}:
      %copy_hands_id(hs) : {Eq.fresh(Eq.Ctx{hs, b, dk, n, k, t}) == Eq.Ctx{_, b, dk, n, k, t} : Eq.Ctx}
      %copy_id(b) : {Eq.fresh(Eq.Ctx{hs, b, dk, n, k, t}) == Eq.Ctx{Eq.copy_hands(hs), _, dk, n, k, t} : Eq.Ctx}
      %copy_id(dk) : {Eq.fresh(Eq.Ctx{hs, b, dk, n, k, t}) == Eq.Ctx{Eq.copy_hands(hs), Eq.copy(b), _, n, k, t} : Eq.Ctx}
      {==}

# The loop over n + m boards from i is the loop over the first m, then the
# loop over the next n.
def seq_add(n: Nat, +m: Nat, +x: Eq.Ctx, +i: Nat) -> {Eq.add(Eq.seq(m, x, i), Eq.seq(n, x, Nat.add(m, i))) == Eq.seq(Nat.add(n, m), x, i) : List<&2, Spec.Tally>}:
  match n:
    case 0n:
      add_nil(Eq.seq(m, x, i))
    case 1n++q:
      %seq_add(q, m, x, i) : {Eq.add(Eq.seq(m, x, i), Eq.add(Eq.seq(q, x, Nat.add(m, i)), Eq.at(x, Nat.add(q, Nat.add(m, i))))) == Eq.add(_, Eq.at(x, Nat.add(Nat.add(q, m), i))) : List<&2, Spec.Tally>}
      %add_assoc(q, m, i) : {Eq.add(Eq.seq(m, x, i), Eq.add(Eq.seq(q, x, Nat.add(m, i)), Eq.at(x, Nat.add(q, Nat.add(m, i))))) == Eq.add(Eq.add(Eq.seq(m, x, i), Eq.seq(q, x, Nat.add(m, i))), Eq.at(x, _)) : List<&2, Spec.Tally>}
      ladd_assoc(Eq.seq(m, x, i), Eq.seq(q, x, Nat.add(m, i)), Eq.at(x, Nat.add(q, Nat.add(m, i))))

def Laws.tree_is_seq(d, c, x, i):
  match d:
    case 0n:
      %fresh_id(x) : {Eq.seq(Comb.pow2(c), Eq.fresh(x), i) == Eq.seq(Comb.pow2(c), _, i) : List<&2, Spec.Tally>}
      {==}
    case 1n++p:
      %seq_add(Comb.pow2(Nat.add(p, c)), Comb.pow2(Nat.add(p, c)), x, i) : {Eq.add(Eq.tree(p, c, x, i), Eq.tree(p, c, x, Nat.add(Comb.pow2(Nat.add(p, c)), i))) == _ : List<&2, Spec.Tally>}
      %Laws.tree_is_seq(p, c, x, i) : {Eq.add(Eq.tree(p, c, x, i), Eq.tree(p, c, x, Nat.add(Comb.pow2(Nat.add(p, c)), i))) == Eq.add(_, Eq.seq(Comb.pow2(Nat.add(p, c)), x, Nat.add(Comb.pow2(Nat.add(p, c)), i))) : List<&2, Spec.Tally>}
      %Laws.tree_is_seq(p, c, x, Nat.add(Comb.pow2(Nat.add(p, c)), i)) : {Eq.add(Eq.tree(p, c, x, i), Eq.tree(p, c, x, Nat.add(Comb.pow2(Nat.add(p, c)), i))) == Eq.add(Eq.tree(p, c, x, i), _) : List<&2, Spec.Tally>}
      {==}
