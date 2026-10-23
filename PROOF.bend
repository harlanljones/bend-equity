import Base
import ./spec.bend as Spec
import ./comb.bend as Comb
import ./eval.bend as Eval
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

# Bool
# ====

def BDisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : BDisc(_)
  Unit{}

def and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {(a && b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({(False{} && b) == True{} : Bool}, false_true(ea))

def and_l(a: Bool, -b: Bool, e: {(a && b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(e))

def and_r(a: Bool, -b: Bool, e: {(a && b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(e))

# Order
# =====

def lt_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_lt(a, b) == True{} : Bool}, e2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, false_true(e1))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(e2))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, false_true(e2))
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, e1, e2)

def le_succ_lt(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, false_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      le_succ_lt(p, q, e)

def le_weaken(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(a, 0n) == True{} : Bool}, false_true(e))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      le_weaken(p, q, e)

def le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

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

# LAW 2
# =====

# Strictly ascending, every element at least n.
def asc_ge(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Nat.is_le(n, h) && asc_ge(t, 1n+h)

def asc_ge_from(t: List<&2, Nat>, +h: Nat, +e: {asc_ge(t, 1n+h) == True{} : Bool}) -> {Spec.ascending_from(t, h) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+h2, t2}:
      and_intro(Nat.is_lt(h, h2), Spec.ascending_from(t2, h2), le_succ_lt(h, h2, and_l(Nat.is_le(1n+h, h2), asc_ge(t2, 1n+h2), e)), asc_ge_from(t2, h2, and_r(Nat.is_le(1n+h, h2), asc_ge(t2, 1n+h2), e)))

def asc_ge_asc(xs: List<&2, Nat>, +n: Nat, +e: {asc_ge(xs, n) == True{} : Bool}) -> {Spec.ascending(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      asc_ge_from(t, h, and_r(Nat.is_le(n, h), asc_ge(t, 1n+h), e))

def asc_ge_weaken(xs: List<&2, Nat>, +p: Nat, +e: {asc_ge(xs, 1n+p) == True{} : Bool}) -> {asc_ge(xs, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      and_intro(Nat.is_le(p, h), asc_ge(t, 1n+h), le_weaken(p, h, and_l(Nat.is_le(1n+p, h), asc_ge(t, 1n+h), e)), and_r(Nat.is_le(1n+p, h), asc_ge(t, 1n+h), e))

def deck_put_asc(kn: Bool, +p: Nat, acc: List<&2, Nat>, +e: {asc_ge(acc, 1n+p) == True{} : Bool}) -> {asc_ge(Comb.deck.put(kn, p, acc), p) == True{} : Bool}:
  match kn:
    case True{}:
      asc_ge_weaken(acc, p, e)
    case False{}:
      and_intro(Nat.is_le(p, p), asc_ge(acc, 1n+p), le_refl(p), e)

def deck_go_asc(n: Nat, +known: List<&2, Nat>, +acc: List<&2, Nat>, +e: {asc_ge(acc, n) == True{} : Bool}) -> {Spec.ascending(Comb.deck.go(n, known, acc)) == True{} : Bool}:
  match n:
    case 0n:
      asc_ge_asc(acc, 0n, e)
    case 1n++p:
      deck_go_asc(p, known, Comb.deck.put(Comb.mem(known, p), p, acc), deck_put_asc(Comb.mem(known, p), p, acc, e))

def deck_asc(+known: List<&2, Nat>) -> {Spec.ascending(Comb.deck(known)) == True{} : Bool}:
  deck_go_asc(52n, known, Nil{}, {==})

def deck_put_lt(kn: Bool, +p: Nat, +acc: List<&2, Nat>, +m: Nat, +ep: {Nat.is_lt(p, m) == True{} : Bool}, +e: {Spec.all_lt(acc, m) == True{} : Bool}) -> {Spec.all_lt(Comb.deck.put(kn, p, acc), m) == True{} : Bool}:
  match kn:
    case True{}:
      e
    case False{}:
      and_intro(Nat.is_lt(p, m), Spec.all_lt(acc, m), ep, e)

def deck_go_lt(n: Nat, +known: List<&2, Nat>, +acc: List<&2, Nat>, +m: Nat, +en: {Nat.is_le(n, m) == True{} : Bool}, +e: {Spec.all_lt(acc, m) == True{} : Bool}) -> {Spec.all_lt(Comb.deck.go(n, known, acc), m) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n++p:
      deck_go_lt(p, known, Comb.deck.put(Comb.mem(known, p), p, acc), m, le_weaken(p, m, en), deck_put_lt(Comb.mem(known, p), p, acc, m, le_succ_lt(p, m, en), e))

def deck_lt(+known: List<&2, Nat>) -> {Spec.all_lt(Comb.deck(known), 52n) == True{} : Bool}:
  deck_go_lt(52n, known, Nil{}, 52n, le_refl(52n), {==})

def asc_from_trans(t: List<&2, Nat>, +a: Nat, +h: Nat, +e1: {Nat.is_lt(a, h) == True{} : Bool}, +e2: {Spec.ascending_from(t, h) == True{} : Bool}) -> {Spec.ascending_from(t, a) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+h2, t2}:
      and_intro(Nat.is_lt(a, h2), Spec.ascending_from(t2, h2), lt_trans(a, h, h2, e1, and_l(Nat.is_lt(h, h2), Spec.ascending_from(t2, h2), e2)), and_r(Nat.is_lt(h, h2), Spec.ascending_from(t2, h2), e2))

def asc_from_asc(t: List<&2, Nat>, +h: Nat, +e: {Spec.ascending_from(t, h) == True{} : Bool}) -> {Spec.ascending(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+h2, t2}:
      and_r(Nat.is_lt(h, h2), Spec.ascending_from(t2, h2), e)

# One step of board: tk says whether it takes the head.
def board_asc_from.step(tk: Bool, +h: Nat, +t: List<&2, Nat>, +m: Nat, +j: Nat, +i: Nat, +b: Nat, +prev: Nat, eh: {Nat.is_lt(prev, h) == True{} : Bool}, e1: {Spec.ascending_from(Comb.board(t, m, j, i), h) == True{} : Bool}, e2: {Spec.ascending_from(Comb.board(t, m, 1n+j, Nat.sub(i, b)), prev) == True{} : Bool}) -> {Spec.ascending_from(Comb.board.put(tk, h, Comb.board(t, m, Comb.board.pick(tk, j, 1n+j), Comb.board.pick(tk, i, Nat.sub(i, b)))), prev) == True{} : Bool}:
  match tk:
    case True{}:
      and_intro(Nat.is_lt(prev, h), Spec.ascending_from(Comb.board(t, m, j, i), h), eh, e1)
    case False{}:
      e2

def board_asc_from(xs: List<&2, Nat>, +n: Nat, +k: Nat, +i: Nat, +prev: Nat, +e: {Spec.ascending_from(xs, prev) == True{} : Bool}) -> {Spec.ascending_from(Comb.board(xs, n, k, i), prev) == True{} : Bool}:
  match xs n k:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n _:
      {==}
    case Con{h, t} 1n+m 0n:
      {==}
    case Con{+h, +t} 1n++m 1n++j:
      +b = Comb.binom(m, j)
      +eh = and_l(Nat.is_lt(prev, h), Spec.ascending_from(t, h), e)
      +et = and_r(Nat.is_lt(prev, h), Spec.ascending_from(t, h), e)
      board_asc_from.step(Nat.is_lt(i, b), h, t, m, j, i, b, prev, eh, board_asc_from(t, m, j, i, h, et), board_asc_from(t, m, 1n+j, Nat.sub(i, b), prev, asc_from_trans(t, prev, h, eh, et)))

def board_asc.step(tk: Bool, +h: Nat, +t: List<&2, Nat>, +m: Nat, +j: Nat, +i: Nat, +b: Nat, e1: {Spec.ascending_from(Comb.board(t, m, j, i), h) == True{} : Bool}, e2: {Spec.ascending(Comb.board(t, m, 1n+j, Nat.sub(i, b))) == True{} : Bool}) -> {Spec.ascending(Comb.board.put(tk, h, Comb.board(t, m, Comb.board.pick(tk, j, 1n+j), Comb.board.pick(tk, i, Nat.sub(i, b))))) == True{} : Bool}:
  match tk:
    case True{}:
      e1
    case False{}:
      e2

def board_asc(xs: List<&2, Nat>, +n: Nat, +k: Nat, +i: Nat, +e: {Spec.ascending(xs) == True{} : Bool}) -> {Spec.ascending(Comb.board(xs, n, k, i)) == True{} : Bool}:
  match xs n k:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n _:
      {==}
    case Con{h, t} 1n+m 0n:
      {==}
    case Con{+h, +t} 1n++m 1n++j:
      +b = Comb.binom(m, j)
      board_asc.step(Nat.is_lt(i, b), h, t, m, j, i, b, board_asc_from(t, m, j, i, h, e), board_asc(t, m, 1n+j, Nat.sub(i, b), asc_from_asc(t, h, e)))

def board_lt.step(tk: Bool, +h: Nat, +t: List<&2, Nat>, +m: Nat, +j: Nat, +i: Nat, +b: Nat, +top: Nat, eh: {Nat.is_lt(h, top) == True{} : Bool}, e1: {Spec.all_lt(Comb.board(t, m, j, i), top) == True{} : Bool}, e2: {Spec.all_lt(Comb.board(t, m, 1n+j, Nat.sub(i, b)), top) == True{} : Bool}) -> {Spec.all_lt(Comb.board.put(tk, h, Comb.board(t, m, Comb.board.pick(tk, j, 1n+j), Comb.board.pick(tk, i, Nat.sub(i, b)))), top) == True{} : Bool}:
  match tk:
    case True{}:
      and_intro(Nat.is_lt(h, top), Spec.all_lt(Comb.board(t, m, j, i), top), eh, e1)
    case False{}:
      e2

def board_lt(xs: List<&2, Nat>, +n: Nat, +k: Nat, +i: Nat, +top: Nat, +e: {Spec.all_lt(xs, top) == True{} : Bool}) -> {Spec.all_lt(Comb.board(xs, n, k, i), top) == True{} : Bool}:
  match xs n k:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n _:
      {==}
    case Con{h, t} 1n+m 0n:
      {==}
    case Con{+h, +t} 1n++m 1n++j:
      +b = Comb.binom(m, j)
      +et = and_r(Nat.is_lt(h, top), Spec.all_lt(t, top), e)
      board_lt.step(Nat.is_lt(i, b), h, t, m, j, i, b, top, and_l(Nat.is_lt(h, top), Spec.all_lt(t, top), e), board_lt(t, m, j, i, top, et), board_lt(t, m, 1n+j, Nat.sub(i, b), top, et))

def Laws.board_well_formed(known, k, i):
  +dk = Comb.deck(known)
  +n = Comb.deck_size(known)
  and_intro(Spec.ascending(Comb.board(dk, n, k, i)), Spec.all_lt(Comb.board(dk, n, k, i), 52n), board_asc(dk, n, k, i, deck_asc(known)), board_lt(dk, n, k, i, 52n, deck_lt(known)))

# LAW 3
# =====

# a implies b.
def imp(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      True{}

def eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_true(e))
    case 1n+p 1n+q:
      %eq_of_is_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def mem_has(xs: List<&2, Nat>, +c: Nat) -> {Comb.mem(xs, c) == Spec.has(xs, c) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %mem_has(t, c) : {Comb.mem(Con{h, t}, c) == (Nat.is_eq(h, c) || _) : Bool}
      {==}

def or_imp(e0: Bool, x: Bool, y: Bool, ih: {imp(x, y) == True{} : Bool}) -> {imp(e0 || x, e0 || y) == True{} : Bool}:
  match e0:
    case True{}:
      {==}
    case False{}:
      ih

def imp_true(x: Bool) -> {imp(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def imp_or_r(x: Bool, e0: Bool, y: Bool, ih: {imp(x, y) == True{} : Bool}) -> {imp(x, e0 || y) == True{} : Bool}:
  match e0:
    case True{}:
      imp_true(x)
    case False{}:
      ih

def board_sub.step(tk: Bool, +h: Nat, +t: List<&2, Nat>, +m: Nat, +j: Nat, +i: Nat, +b: Nat, +c: Nat, e1: {imp(Spec.has(Comb.board(t, m, j, i), c), Spec.has(t, c)) == True{} : Bool}, e2: {imp(Spec.has(Comb.board(t, m, 1n+j, Nat.sub(i, b)), c), Spec.has(t, c)) == True{} : Bool}) -> {imp(Spec.has(Comb.board.put(tk, h, Comb.board(t, m, Comb.board.pick(tk, j, 1n+j), Comb.board.pick(tk, i, Nat.sub(i, b)))), c), Spec.has(Con{h, t}, c)) == True{} : Bool}:
  match tk:
    case True{}:
      or_imp(Nat.is_eq(h, c), Spec.has(Comb.board(t, m, j, i), c), Spec.has(t, c), e1)
    case False{}:
      imp_or_r(Spec.has(Comb.board(t, m, 1n+j, Nat.sub(i, b)), c), Nat.is_eq(h, c), Spec.has(t, c), e2)

# A board holds only cards of its deck.
def board_sub(xs: List<&2, Nat>, +n: Nat, +k: Nat, +i: Nat, +c: Nat) -> {imp(Spec.has(Comb.board(xs, n, k, i), c), Spec.has(xs, c)) == True{} : Bool}:
  match xs n k:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n _:
      {==}
    case Con{h, t} 1n+m 0n:
      {==}
    case Con{+h, +t} 1n++m 1n++j:
      +b = Comb.binom(m, j)
      board_sub.step(Nat.is_lt(i, b), h, t, m, j, i, b, c, board_sub(t, m, j, i, c), board_sub(t, m, 1n+j, Nat.sub(i, b), c))

def deck_put_out.hit(e0: Bool, +p: Nat, +c: Nat, +known: List<&2, Nat>, acc: List<&2, Nat>, ee: {Nat.is_eq(p, c) == e0 : Bool}, ek: {Comb.mem(known, p) == False{} : Bool}, e: {imp(Spec.has(acc, c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}) -> {imp(e0 || Spec.has(acc, c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}:
  match e0:
    case True{}:
      %eq_of_is_eq(p, c, ee) : {Spec.not_(Comb.mem(known, _)) == True{} : Bool}
      %Equal.sym(Bool, Comb.mem(known, p), False{}, ek) : {Spec.not_(_) == True{} : Bool}
      {==}
    case False{}:
      e

def deck_put_out(kn: Bool, +p: Nat, +acc: List<&2, Nat>, +c: Nat, +known: List<&2, Nat>, ek: {Comb.mem(known, p) == kn : Bool}, e: {imp(Spec.has(acc, c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}) -> {imp(Spec.has(Comb.deck.put(kn, p, acc), c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}:
  match kn:
    case True{}:
      e
    case False{}:
      deck_put_out.hit(Nat.is_eq(p, c), p, c, known, acc, {==}, ek, e)

def deck_go_out(n: Nat, +known: List<&2, Nat>, +acc: List<&2, Nat>, +c: Nat, e: {imp(Spec.has(acc, c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}) -> {imp(Spec.has(Comb.deck.go(n, known, acc), c), Spec.not_(Comb.mem(known, c))) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n++p:
      deck_go_out(p, known, Comb.deck.put(Comb.mem(known, p), p, acc), c, deck_put_out(Comb.mem(known, p), p, acc, c, known, {==}, e))

# A deck holds no known card.
def deck_out(+known: List<&2, Nat>, +c: Nat) -> {imp(Spec.has(Comb.deck(known), c), Spec.not_(Spec.has(known, c))) == True{} : Bool}:
  %mem_has(known, c) : {imp(Spec.has(Comb.deck(known), c), Spec.not_(_)) == True{} : Bool}
  deck_go_out(52n, known, Nil{}, c, {==})

def avoid(a: Bool, b: Bool, d: Bool, e1: {imp(a, b) == True{} : Bool}, e2: {imp(b, Spec.not_(d)) == True{} : Bool}) -> {(a && d) == False{} : Bool}:
  match a b d:
    case False{} _ _:
      {==}
    case True{} False{} _:
      Empty.absurd({(True{} && d) == False{} : Bool}, false_true(e1))
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      Empty.absurd({(True{} && True{}) == False{} : Bool}, false_true(e2))

def Laws.board_avoids_known(known, k, i, c):
  +dk = Comb.deck(known)
  +n = Comb.deck_size(known)
  avoid(Spec.has(Comb.board(dk, n, k, i), c), Spec.has(dk, c), Spec.has(known, c), board_sub(dk, n, k, i, c), deck_out(known, c))

# LAW 4
# =====

def or4_swap(a: Bool, b: Bool, c: Bool, d: Bool, -m: Bool) -> {(a || (b || (c || (d || m)))) == (c || (d || (a || (b || m)))) : Bool}:
  match a b c d:
    case True{} _ True{} _:
      {==}
    case True{} _ False{} True{}:
      {==}
    case True{} _ False{} False{}:
      {==}
    case False{} True{} True{} _:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} _ _:
      {==}

# The known cards of p, q and of q, p hold the same cards.
def mem_swap(+px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +c: Nat) -> {Comb.mem(px <> py <> qx <> qy <> b, c) == Comb.mem(qx <> qy <> px <> py <> b, c) : Bool}:
  or4_swap(Nat.is_eq(px, c), Nat.is_eq(py, c), Nat.is_eq(qx, c), Nat.is_eq(qy, c), Comb.mem(b, c))

def deck_go_swap(n: Nat, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +acc: List<&2, Nat>) -> {Comb.deck.go(n, px <> py <> qx <> qy <> b, acc) == Comb.deck.go(n, qx <> qy <> px <> py <> b, acc) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++r:
      %mem_swap(px, py, qx, qy, b, r) : {Comb.deck.go(r, px <> py <> qx <> qy <> b, Comb.deck.put(Comb.mem(px <> py <> qx <> qy <> b, r), r, acc)) == Comb.deck.go(r, qx <> qy <> px <> py <> b, Comb.deck.put(_, r, acc)) : List<&2, Nat>}
      deck_go_swap(r, px, py, qx, qy, b, Comb.deck.put(Comb.mem(px <> py <> qx <> qy <> b, r), r, acc))

def size_go_swap(n: Nat, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>) -> {Comb.deck_size.go(n, px <> py <> qx <> qy <> b) == Comb.deck_size.go(n, qx <> qy <> px <> py <> b) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++r:
      %mem_swap(px, py, qx, qy, b, r) : {Nat.add(Comb.deck_size.one(Comb.mem(px <> py <> qx <> qy <> b, r)), Comb.deck_size.go(r, px <> py <> qx <> qy <> b)) == Nat.add(Comb.deck_size.one(_), Comb.deck_size.go(r, qx <> qy <> px <> py <> b)) : Nat}
      %size_go_swap(r, px, py, qx, qy, b) : {Nat.add(Comb.deck_size.one(Comb.mem(px <> py <> qx <> qy <> b, r)), Comb.deck_size.go(r, px <> py <> qx <> qy <> b)) == Nat.add(Comb.deck_size.one(Comb.mem(px <> py <> qx <> qy <> b, r)), _) : Nat}
      {==}

# The spot q, p has the deck of the spot p, q.
def ctx_swap(+px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>) -> {Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, Comb.deck(px <> py <> qx <> qy <> b), Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)))} == Eq.ctx(Spec.Spot{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b}) : Eq.Ctx}:
  %deck_go_swap(52n, px, py, qx, qy, b, Nil{}) : {Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, Comb.deck(px <> py <> qx <> qy <> b), Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)))} == Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, _, Comb.deck_size(qx <> qy <> px <> py <> b), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(qx <> qy <> px <> py <> b), Nat.sub(5n, Spec.len(b)))} : Eq.Ctx}
  %size_go_swap(52n, px, py, qx, qy, b) : {Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, Comb.deck(px <> py <> qx <> qy <> b), Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)))} == Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, Comb.deck(px <> py <> qx <> qy <> b), _, Nat.sub(5n, Spec.len(b)), Comb.binom(_, Nat.sub(5n, Spec.len(b)))} : Eq.Ctx}
  {==}

def zero_max(x: Nat) -> {x == Nat.max(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def max_comm(a: Nat, b: Nat) -> {Nat.max(a, b) == Nat.max(b, a) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %max_comm(p, q) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

def maxl2_comm(+a: Nat, +b: Nat) -> {Eq.maxl([a, b]) == Eq.maxl([b, a]) : Nat}:
  %zero_max(b) : {Nat.max(a, _) == Nat.max(b, Nat.max(a, 0n)) : Nat}
  %zero_max(a) : {Nat.max(a, b) == Nat.max(b, _) : Nat}
  max_comm(a, b)

def add01(u: Bool, v: Bool) -> {Nat.add(Eq.b2n(u), Nat.add(Eq.b2n(v), 0n)) == Nat.add(Eq.b2n(v), Nat.add(Eq.b2n(u), 0n)) : Nat}:
  match u v:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def cnt2_comm(+a: Nat, +b: Nat, +m: Nat) -> {Eq.cnt([a, b], m) == Eq.cnt([b, a], m) : Nat}:
  add01(Nat.is_eq(a, m), Nat.is_eq(b, m))

def tallies2(+a: Nat, +b: Nat, +m1: Nat, +m2: Nat, e: {m1 == m2 : Nat}) -> {Eq.tallies([a, b], m1, Nat.is_eq(Eq.cnt([a, b], m1), 1n), Nat.div(2520n, Eq.cnt([a, b], m1))) == Spec.swap2(Eq.tallies([b, a], m2, Nat.is_eq(Eq.cnt([b, a], m2), 1n), Nat.div(2520n, Eq.cnt([b, a], m2)))) : List<&2, Spec.Tally>}:
  %e : {Eq.tallies([a, b], m1, Nat.is_eq(Eq.cnt([a, b], m1), 1n), Nat.div(2520n, Eq.cnt([a, b], m1))) == Spec.swap2(Eq.tallies([b, a], _, Nat.is_eq(Eq.cnt([b, a], _), 1n), Nat.div(2520n, Eq.cnt([b, a], _)))) : List<&2, Spec.Tally>}
  %cnt2_comm(a, b, m1) : {Eq.tallies([a, b], m1, Nat.is_eq(Eq.cnt([a, b], m1), 1n), Nat.div(2520n, Eq.cnt([a, b], m1))) == Spec.swap2(Eq.tallies([b, a], m1, Nat.is_eq(_, 1n), Nat.div(2520n, _))) : List<&2, Spec.Tally>}
  {==}

# Judging two scores in the other order swaps the two tallies.
def judge_swap(+a: Nat, +b: Nat) -> {Eq.judge([a, b]) == Spec.swap2(Eq.judge([b, a])) : List<&2, Spec.Tally>}:
  tallies2(a, b, Eq.maxl([a, b]), Eq.maxl([b, a]), maxl2_comm(a, b))

def at_go_swap(ok: Bool, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +j: Nat) -> {Spec.swap2(Eq.at.go(ok, [Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, j)) == Eq.at.go(ok, [Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, dk, n, k, j) : List<&2, Spec.Tally>}:
  match ok:
    case True{}:
      +full = Eq.cat(b, Comb.board(dk, n, k, j))
      +sp = Eval.score7(px, py, full)
      +sq = Eval.score7(qx, qy, full)
      Equal.sym(List<&2, Spec.Tally>, Eq.judge([sq, sp]), Spec.swap2(Eq.judge([sp, sq])), judge_swap(sq, sp))
    case False{}:
      {==}

# Nil or exactly two tallies.
def two(ts: List<&2, Spec.Tally>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{a, Nil{}}:
      False{}
    case Con{a, Con{b, Nil{}}}:
      True{}
    case Con{a, Con{b, Con{c, r}}}:
      False{}

def two_add(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>, ea: {two(a) == True{} : Bool}, eb: {two(b) == True{} : Bool}) -> {two(Eq.add(a, b)) == True{} : Bool}:
  match a b:
    case Nil{} _:
      eb
    case Con{x, Nil{}} _:
      Empty.absurd({two(Eq.add(Con{x, Nil{}}, b)) == True{} : Bool}, false_true(ea))
    case Con{x, Con{y, Con{z, r}}} _:
      Empty.absurd({two(Eq.add(Con{x, Con{y, Con{z, r}}}, b)) == True{} : Bool}, false_true(ea))
    case Con{x, Con{y, Nil{}}} Nil{}:
      {==}
    case Con{x, Con{y, Nil{}}} Con{u, Nil{}}:
      Empty.absurd({two(Eq.add(Con{x, Con{y, Nil{}}}, Con{u, Nil{}})) == True{} : Bool}, false_true(eb))
    case Con{x, Con{y, Nil{}}} Con{u, Con{v, Nil{}}}:
      {==}
    case Con{x, Con{y, Nil{}}} Con{u, Con{v, Con{w, r}}}:
      Empty.absurd({two(Eq.add(Con{x, Con{y, Nil{}}}, Con{u, Con{v, Con{w, r}}})) == True{} : Bool}, false_true(eb))

def swap_add(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>, ea: {two(a) == True{} : Bool}, eb: {two(b) == True{} : Bool}) -> {Eq.add(Spec.swap2(a), Spec.swap2(b)) == Spec.swap2(Eq.add(a, b)) : List<&2, Spec.Tally>}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, Nil{}} _:
      Empty.absurd({Eq.add(Spec.swap2(Con{x, Nil{}}), Spec.swap2(b)) == Spec.swap2(Eq.add(Con{x, Nil{}}, b)) : List<&2, Spec.Tally>}, false_true(ea))
    case Con{x, Con{y, Con{z, r}}} _:
      Empty.absurd({Eq.add(Spec.swap2(Con{x, Con{y, Con{z, r}}}), Spec.swap2(b)) == Spec.swap2(Eq.add(Con{x, Con{y, Con{z, r}}}, b)) : List<&2, Spec.Tally>}, false_true(ea))
    case Con{x, Con{y, Nil{}}} Nil{}:
      {==}
    case Con{x, Con{y, Nil{}}} Con{u, Nil{}}:
      Empty.absurd({Eq.add(Spec.swap2(Con{x, Con{y, Nil{}}}), Spec.swap2(Con{u, Nil{}})) == Spec.swap2(Eq.add(Con{x, Con{y, Nil{}}}, Con{u, Nil{}})) : List<&2, Spec.Tally>}, false_true(eb))
    case Con{x, Con{y, Nil{}}} Con{u, Con{v, Nil{}}}:
      {==}
    case Con{x, Con{y, Nil{}}} Con{u, Con{v, Con{w, r}}}:
      Empty.absurd({Eq.add(Spec.swap2(Con{x, Con{y, Nil{}}}), Spec.swap2(Con{u, Con{v, Con{w, r}}})) == Spec.swap2(Eq.add(Con{x, Con{y, Nil{}}}, Con{u, Con{v, Con{w, r}}})) : List<&2, Spec.Tally>}, false_true(eb))

def two_at(ok: Bool, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +j: Nat) -> {two(Eq.at.go(ok, [Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, j)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def two_seq(m: Nat, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +i: Nat) -> {two(Eq.seq(m, Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t}, i)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++r:
      +x = {Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t} : Eq.Ctx}
      two_add(Eq.seq(r, x, i), Eq.at(x, Nat.add(r, i)), two_seq(r, px, py, qx, qy, b, dk, n, k, t, i), two_at(Nat.is_lt(Nat.add(r, i), t), px, py, qx, qy, b, dk, n, k, Nat.add(r, i)))

def seq_swap(m: Nat, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +i: Nat) -> {Spec.swap2(Eq.seq(m, Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t}, i)) == Eq.seq(m, Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, dk, n, k, t}, i) : List<&2, Spec.Tally>}:
  match m:
    case 0n:
      {==}
    case 1n++r:
      +x = {Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t} : Eq.Ctx}
      +y = {Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, dk, n, k, t} : Eq.Ctx}
      %seq_swap(r, px, py, qx, qy, b, dk, n, k, t, i) : {Spec.swap2(Eq.add(Eq.seq(r, x, i), Eq.at(x, Nat.add(r, i)))) == Eq.add(_, Eq.at(y, Nat.add(r, i))) : List<&2, Spec.Tally>}
      %at_go_swap(Nat.is_lt(Nat.add(r, i), t), px, py, qx, qy, b, dk, n, k, Nat.add(r, i)) : {Spec.swap2(Eq.add(Eq.seq(r, x, i), Eq.at(x, Nat.add(r, i)))) == Eq.add(Spec.swap2(Eq.seq(r, x, i)), _) : List<&2, Spec.Tally>}
      Equal.sym(List<&2, Spec.Tally>, Eq.add(Spec.swap2(Eq.seq(r, x, i)), Spec.swap2(Eq.at(x, Nat.add(r, i)))), Spec.swap2(Eq.add(Eq.seq(r, x, i), Eq.at(x, Nat.add(r, i)))), swap_add(Eq.seq(r, x, i), Eq.at(x, Nat.add(r, i)), two_seq(r, px, py, qx, qy, b, dk, n, k, t, i), two_at(Nat.is_lt(Nat.add(r, i), t), px, py, qx, qy, b, dk, n, k, Nat.add(r, i))))

def tree_swap(+d: Nat, +c: Nat, +px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +i: Nat) -> {Eq.tree(d, c, Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, dk, n, k, t}, i) == Spec.swap2(Eq.tree(d, c, Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t}, i)) : List<&2, Spec.Tally>}:
  +x = {Eq.Ctx{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b, dk, n, k, t} : Eq.Ctx}
  +y = {Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, dk, n, k, t} : Eq.Ctx}
  +m = Comb.pow2(Nat.add(d, c))
  %Equal.sym(List<&2, Spec.Tally>, Eq.tree(d, c, y, i), Eq.seq(m, y, i), Laws.tree_is_seq(d, c, y, i)) : {_ == Spec.swap2(Eq.tree(d, c, x, i)) : List<&2, Spec.Tally>}
  %Equal.sym(List<&2, Spec.Tally>, Eq.tree(d, c, x, i), Eq.seq(m, x, i), Laws.tree_is_seq(d, c, x, i)) : {Eq.seq(m, y, i) == Spec.swap2(_) : List<&2, Spec.Tally>}
  Equal.sym(List<&2, Spec.Tally>, Spec.swap2(Eq.seq(m, x, i)), Eq.seq(m, y, i), seq_swap(m, px, py, qx, qy, b, dk, n, k, t, i))

# run on q, p, with the deck rewritten to that of p, q, is a tree over the same range.
def run_swap(+px: Nat, +py: Nat, +qx: Nat, +qy: Nat, +b: List<&2, Nat>) -> {Eq.run.cpu(Eq.Ctx{[Spec.Hand{qx, qy}, Spec.Hand{px, py}], b, Comb.deck(px <> py <> qx <> qy <> b), Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(px <> py <> qx <> qy <> b), Nat.sub(5n, Spec.len(b)))}) == Spec.swap2(Eq.run.cpu(Eq.ctx(Spec.Spot{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b}))) : List<&2, Spec.Tally>}:
  +known = {px <> py <> qx <> qy <> b : List<&2, Nat>}
  +n = Comb.deck_size(known)
  +k = Nat.sub(5n, Spec.len(b))
  +t = Comb.binom(n, k)
  +dd = Comb.clog2(t)
  +d = Nat.min(dd, 14n)
  tree_swap(d, Nat.sub(dd, d), px, py, qx, qy, b, Comb.deck(known), n, k, t, 0n)

def Laws.heads_up_swap(g, p, q, b):
  match g p q:
    case True{} Spec.Hand{+px, +py} Spec.Hand{+qx, +qy}:
      %ctx_swap(px, py, qx, qy, b) : {Eq.run.gpu(_) == Spec.swap2(Eq.run.gpu(Eq.ctx(Spec.Spot{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b}))) : List<&2, Spec.Tally>}
      run_swap(px, py, qx, qy, b)
    case False{} Spec.Hand{+px, +py} Spec.Hand{+qx, +qy}:
      %ctx_swap(px, py, qx, qy, b) : {Eq.run.cpu(_) == Spec.swap2(Eq.run.cpu(Eq.ctx(Spec.Spot{[Spec.Hand{px, py}, Spec.Hand{qx, qy}], b}))) : List<&2, Spec.Tally>}
      run_swap(px, py, qx, qy, b)

# LAW 5 and LAW 6
# ===============
# Both laws take `ok` live (`for ok:`): Bend 2.0.38 lets no live proof use an
# erased hypothesis (a rewrite with ok, or ok as a live argument, is refused:
# "expected : -ok, observed : ok"), and neither claim holds without it.
# tally_total_live and share_total_live below are the proofs; each law is its
# lemma applied to (g, s, ok).

# Arithmetic
# ----------

def NDisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_succ(-x: Nat, e: {0n == 1n+x : Nat}) -> Empty:
  %e : NDisc(_)
  Unit{}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_one(a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# (a + b) + (c + d) == (a + c) + (b + d)
def add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %add_assoc(a, c, Nat.add(b, d)) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(c, Nat.add(b, d)), Nat.add(Nat.add(c, b), d), add_assoc(c, b, d)) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  %add_comm(b, c) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, Nat.add(_, d)) : Nat}
  %add_assoc(b, c, d) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  Equal.sym(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, b), Nat.add(c, d)), add_assoc(a, b, Nat.add(c, d)))

def mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_succ(a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_succ(p, b)) : {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %Equal.sym(Nat, Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(Nat.add(b, p), Nat.mul(p, b)), add_assoc(b, p, Nat.mul(p, b))) : {1n+_ == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %add_comm(p, b) : {1n+Nat.add(_, Nat.mul(p, b)) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %Equal.sym(Nat, Nat.add(p, Nat.add(b, Nat.mul(p, b))), Nat.add(Nat.add(p, b), Nat.mul(p, b)), add_assoc(p, b, Nat.mul(p, b))) : {1n+Nat.add(Nat.add(p, b), Nat.mul(p, b)) == 1n+_ : Nat}
      {==}

def mul_comm(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

def eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

# Order and subtraction
# ---------------------

def le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      le_succ_r(p, q, e)

def le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, false_true(e1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, false_true(e2))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, e1, e2)

def le_add_l(p: Nat, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(p, b)) == True{} : Bool}:
  match p:
    case 0n:
      e
    case 1n++q:
      le_succ_r(a, Nat.add(q, b), le_add_l(q, a, b, e))

def le_add_r_mono(a: Nat, c: Nat, +b: Nat, e: {Nat.is_le(a, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, b)) == True{} : Bool}:
  match a c:
    case 0n 0n:
      le_refl(b)
    case 0n 1n+q:
      le_add_l(1n+q, b, b, le_refl(b))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, b), b) == True{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      le_add_r_mono(p, q, b, e)

def le_add_l_mono(c: Nat, -b: Nat, -d: Nat, e: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, b), Nat.add(c, d)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+r:
      le_add_l_mono(r, b, d, e)

def le_add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, e1: {Nat.is_le(a, c) == True{} : Bool}, e2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), le_add_r_mono(a, c, b, e1), le_add_l_mono(c, b, d, e2))

def not_lt_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      not_lt_of_le(p, q, e)

def sub_zero_r(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def add_sub(+a: Nat, b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      sub_zero_r(a)
    case 1n+q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), add_succ(a, q)) : {Nat.sub(_, 1n+q) == a : Nat}
      add_sub(a, q)

def sub_of_add(+a: Nat, +b: Nat, -c: Nat, e: {Nat.add(a, b) == c : Nat}) -> {a == Nat.sub(c, b) : Nat}:
  %e : {a == Nat.sub(_, b) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(a, b), b), a, add_sub(a, b))

def sub_le(n: Nat, b: Nat) -> {Nat.is_le(Nat.sub(n, b), n) == True{} : Bool}:
  match n b:
    case 0n _:
      {==}
    case 1n+p 0n:
      le_refl(1n+p)
    case 1n++p 1n++q:
      le_succ_r(Nat.sub(p, q), p, sub_le(p, q))

def sub_anti(a: Nat, b: Nat, +n: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(n, b), Nat.sub(n, a)) == True{} : Bool}:
  match a b:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, sub_zero_r(n)) : {Nat.is_le(Nat.sub(n, b), _) == True{} : Bool}
      sub_le(n, b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.sub(n, 0n), Nat.sub(n, 1n+p)) == True{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      match n:
        case 0n:
          {==}
        case 1n+m:
          sub_anti(p, q, m, e)

def min_sub(a: Nat, b: Nat) -> {Nat.add(Nat.min(a, b), Nat.sub(a, Nat.min(a, b))) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.min(p, q), Nat.sub(p, Nat.min(p, q))), p, min_sub(p, q))

def pow2_pos(n: Nat) -> {Nat.is_le(1n, Comb.pow2(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      +h = Comb.pow2(p)
      le_add_mono(1n, 0n, h, h, pow2_pos(p), le_zero(h))

def pow2_ge(n: Nat) -> {Nat.is_le(n, Comb.pow2(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      +h = Comb.pow2(p)
      le_add_mono(1n, p, h, h, pow2_pos(p), pow2_ge(p))

def cl_if(u: Bool, -d: Nat, -g: Nat, -n: Nat, eu: {Nat.is_le(n, Comb.pow2(d)) == u : Bool}, ih: {Nat.is_le(n, Comb.pow2(Comb.clog2.go(g, n, 1n+d))) == True{} : Bool}) -> {Nat.is_le(n, Comb.pow2(Comb.clog2.if(d, w => Comb.clog2.go(g, n, 1n+d), u))) == True{} : Bool}:
  match u:
    case True{}:
      eu
    case False{}:
      ih

def cl_shift(+g: Nat, +d: Nat, -n: Nat, e: {Nat.is_le(n, Comb.pow2(Nat.add(1n+g, d))) == True{} : Bool}) -> {Nat.is_le(n, Comb.pow2(Nat.add(g, 1n+d))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(g, 1n+d), 1n+Nat.add(g, d), add_succ(g, d)) : {Nat.is_le(n, Comb.pow2(_)) == True{} : Bool}
  e

def cl_go(f: Nat, +n: Nat, +d: Nat, e: {Nat.is_le(n, Comb.pow2(Nat.add(f, d))) == True{} : Bool}) -> {Nat.is_le(n, Comb.pow2(Comb.clog2.go(f, n, d))) == True{} : Bool}:
  match f:
    case 0n:
      e
    case 1n++g:
      cl_if(Nat.is_le(n, Comb.pow2(d)), d, g, n, {==}, cl_go(g, n, 1n+d, cl_shift(g, d, n, e)))

# The search ends on a power of two at least n.
def clog2_ge(+n: Nat) -> {Nat.is_le(n, Comb.pow2(Comb.clog2(n))) == True{} : Bool}:
  cl_go(n, n, 0n, (%Equal.sym(Nat, Nat.add(n, 0n), n, add_zero(n)) : {Nat.is_le(n, Comb.pow2(_)) == True{} : Bool}; pow2_ge(n)))

# One board
# ---------

def TDisc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : TDisc(_)
  Unit{}

def scores_len(hs: List<&2, Spec.Hand>, +full: List<&2, Nat>) -> {Spec.len(Eq.scores(hs, full)) == Spec.count(hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{Spec.Hand{x, y}, t}:
      Equal.cong(Nat, Nat, z => 1n+z, Spec.len(Eq.scores(t, full)), Spec.count(t), scores_len(t, full))

def tcount_tallies(xs: List<&2, Nat>, +m: Nat, +so: Bool, +sh: Nat) -> {Spec.tcount(Eq.tallies(xs, m, so, sh)) == Spec.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, z => 1n+z, Spec.tcount(Eq.tallies(t, m, so, sh)), Spec.len(t), tcount_tallies(t, m, so, sh))

# A board gives one tally per hand.
def tcount_outcome(+hs: List<&2, Spec.Hand>, +full: List<&2, Nat>) -> {Spec.tcount(Eq.outcome(hs, full)) == Spec.count(hs) : Nat}:
  +ss = Eq.scores(hs, full)
  +mx = Eq.maxl(ss)
  +w = Eq.cnt(ss, mx)
  Equal.trans(Nat, Spec.tcount(Eq.outcome(hs, full)), Spec.len(ss), Spec.count(hs), tcount_tallies(ss, mx, Nat.is_eq(w, 1n), Nat.div(2520n, w)), scores_len(hs, full))

def all_one_cons(u: Bool, so: Bool, -sh: Nat, -rest: List<&2, Spec.Tally>, e: {Spec.all_sum(rest, 1n) == True{} : Bool}) -> {Spec.all_sum(Con{Eq.tally(u, so, sh), rest}, 1n) == True{} : Bool}:
  match u so:
    case True{} True{}:
      e
    case True{} False{}:
      e
    case False{} _:
      e

def all_one_tallies(xs: List<&2, Nat>, +m: Nat, +so: Bool, +sh: Nat) -> {Spec.all_sum(Eq.tallies(xs, m, so, sh), 1n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      all_one_cons(Nat.is_eq(h, m), so, sh, Eq.tallies(t, m, so, sh), all_one_tallies(t, m, so, sh))

# A board counts once for every hand: win + tie + lose == 1.
def all_one_outcome(+hs: List<&2, Spec.Hand>, +full: List<&2, Nat>) -> {Spec.all_sum(Eq.outcome(hs, full), 1n) == True{} : Bool}:
  +ss = Eq.scores(hs, full)
  +mx = Eq.maxl(ss)
  +w = Eq.cnt(ss, mx)
  all_one_tallies(ss, mx, Nat.is_eq(w, 1n), Nat.div(2520n, w))

def share_cons(u: Bool, so: Bool, +sh: Nat, -rest: List<&2, Spec.Tally>, -c: Nat, e: {Spec.share_sum(rest) == Nat.mul(c, sh) : Nat}) -> {Spec.share_sum(Con{Eq.tally(u, so, sh), rest}) == Nat.mul(Nat.add(Eq.b2n(u), c), sh) : Nat}:
  match u so:
    case True{} True{}:
      Equal.cong(Nat, Nat, z => Nat.add(sh, z), Spec.share_sum(rest), Nat.mul(c, sh), e)
    case True{} False{}:
      Equal.cong(Nat, Nat, z => Nat.add(sh, z), Spec.share_sum(rest), Nat.mul(c, sh), e)
    case False{} _:
      e

def share_tallies(xs: List<&2, Nat>, +m: Nat, +so: Bool, +sh: Nat) -> {Spec.share_sum(Eq.tallies(xs, m, so, sh)) == Nat.mul(Eq.cnt(xs, m), sh) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      share_cons(Nat.is_eq(h, m), so, sh, Eq.tallies(t, m, so, sh), Eq.cnt(t, m), share_tallies(t, m, so, sh))

def cle_cons(u: Bool, +c: Nat, +l: Nat, e: {Nat.is_le(c, l) == True{} : Bool}) -> {Nat.is_le(Nat.add(Eq.b2n(u), c), 1n+l) == True{} : Bool}:
  match u:
    case True{}:
      e
    case False{}:
      le_succ_r(c, l, e)

def cnt_le_len(xs: List<&2, Nat>, +m: Nat) -> {Nat.is_le(Eq.cnt(xs, m), Spec.len(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      cle_cons(Nat.is_eq(h, m), Eq.cnt(t, m), Spec.len(t), cnt_le_len(t, m))

def max_l(a: Nat, b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.max(0n, 1n+q) == 0n : Nat}, false_true(e))
    case 1n+p 0n:
      {==}
    case 1n++p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(p, q), p, max_l(p, q, e))

def max_r(a: Nat, b: Nat, e: {Nat.is_le(b, a) == False{} : Bool}) -> {Nat.max(a, b) == b : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.max(1n+p, 0n) == 0n : Nat}, true_false(e))
    case 1n+p 1n++q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(p, q), q, max_r(p, q, e))

def cnt_pos.split(u: Bool, +h: Nat, +t: List<&2, Nat>, eu: {Nat.is_le(Eq.maxl(t), h) == u : Bool}, ih: {Nat.is_le(1n, Eq.cnt(t, Eq.maxl(t))) == True{} : Bool}) -> {Nat.is_le(1n, Eq.cnt(Con{h, t}, Eq.maxl(Con{h, t}))) == True{} : Bool}:
  match u:
    case True{}:
      %Equal.sym(Nat, Nat.max(h, Eq.maxl(t)), h, max_l(h, Eq.maxl(t), eu)) : {Nat.is_le(1n, Nat.add(Eq.b2n(Nat.is_eq(h, _)), Eq.cnt(t, _))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, eq_refl(h)) : {Nat.is_le(1n, Nat.add(Eq.b2n(_), Eq.cnt(t, h))) == True{} : Bool}
      le_zero(Eq.cnt(t, h))
    case False{}:
      %Equal.sym(Nat, Nat.max(h, Eq.maxl(t)), Eq.maxl(t), max_r(h, Eq.maxl(t), eu)) : {Nat.is_le(1n, Nat.add(Eq.b2n(Nat.is_eq(h, _)), Eq.cnt(t, _))) == True{} : Bool}
      le_add_l(Eq.b2n(Nat.is_eq(h, Eq.maxl(t))), 1n, Eq.cnt(t, Eq.maxl(t)), ih)

# Some hand holds the best score.
def cnt_pos(t: List<&2, Nat>, +h: Nat) -> {Nat.is_le(1n, Eq.cnt(Con{h, t}, Eq.maxl(Con{h, t}))) == True{} : Bool}:
  match t:
    case Nil{}:
      %zero_max(h) : {Nat.is_le(1n, Nat.add(Eq.b2n(Nat.is_eq(h, _)), 0n)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, eq_refl(h)) : {Nat.is_le(1n, Nat.add(Eq.b2n(_), 0n)) == True{} : Bool}
      {==}
    case Con{+h2, +t2}:
      cnt_pos.split(Nat.is_le(Eq.maxl(Con{h2, t2}), h), h, Con{h2, t2}, {==}, cnt_pos(t2, h2))

# 2520 = lcm(1..10): w winners take 2520 / w each, and nothing is left.
def ten(w: Nat, e1: {Nat.is_le(1n, w) == True{} : Bool}, e2: {Nat.is_le(w, 10n) == True{} : Bool}) -> {Nat.mul(w, Nat.div(2520n, w)) == 2520n : Nat}:
  match w:
    case 0n:
      Empty.absurd({Nat.mul(0n, Nat.div(2520n, 0n)) == 2520n : Nat}, false_true(e1))
    case 1n+w1:
      match w1:
        case 0n:
          {==}
        case 1n+w2:
          match w2:
            case 0n:
              {==}
            case 1n+w3:
              match w3:
                case 0n:
                  {==}
                case 1n+w4:
                  match w4:
                    case 0n:
                      {==}
                    case 1n+w5:
                      match w5:
                        case 0n:
                          {==}
                        case 1n+w6:
                          match w6:
                            case 0n:
                              {==}
                            case 1n+w7:
                              match w7:
                                case 0n:
                                  {==}
                                case 1n+w8:
                                  match w8:
                                    case 0n:
                                      {==}
                                    case 1n+w9:
                                      match w9:
                                        case 0n:
                                          {==}
                                        case 1n+w10:
                                          match w10:
                                            case 0n:
                                              {==}
                                            case 1n+w11:
                                              Empty.absurd({Nat.mul(11n+w11, Nat.div(2520n, 11n+w11)) == 2520n : Nat}, false_true(e2))

# The pot of one board: the shares of its hands add to 2520.
def share_board(hs: List<&2, Spec.Hand>, +full: List<&2, Nat>, e2: {Nat.is_le(2n, Spec.count(hs)) == True{} : Bool}, e10: {Nat.is_le(Spec.count(hs), 10n) == True{} : Bool}) -> {Spec.share_sum(Eq.outcome(hs, full)) == 2520n : Nat}:
  match hs:
    case Nil{}:
      Empty.absurd({Spec.share_sum(Eq.outcome(Nil{}, full)) == 2520n : Nat}, false_true(e2))
    case Con{Spec.Hand{+x, +y}, +t}:
      +hs2 = {Con{Spec.Hand{x, y}, t} : List<&2, Spec.Hand>}
      +ss = Eq.scores(hs2, full)
      +mx = Eq.maxl(ss)
      +w = Eq.cnt(ss, mx)
      +lo = cnt_pos(Eq.scores(t, full), Eval.score7(x, y, full))
      +hi = le_trans(w, Spec.len(ss), 10n, cnt_le_len(ss, mx), (%Equal.sym(Nat, Spec.len(ss), Spec.count(hs2), scores_len(hs2, full)) : {Nat.is_le(_, 10n) == True{} : Bool}; e10))
      Equal.trans(Nat, Spec.share_sum(Eq.outcome(hs2, full)), Nat.mul(w, Nat.div(2520n, w)), 2520n, share_tallies(ss, mx, Nat.is_eq(w, 1n), Nat.div(2520n, w)), ten(w, lo, hi))

# Every board of a spot
# ---------------------
# x = Ctx{hs, b, dk, n, k, t}: board j < t is outcome(hs, ...), past t Nil.

def share_at.go(ok: Bool, e: {ok == True{} : Bool}, hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +j: Nat, e2: {Nat.is_le(2n, Spec.count(hs)) == True{} : Bool}, e10: {Nat.is_le(Spec.count(hs), 10n) == True{} : Bool}) -> {Spec.share_sum(Eq.at.go(ok, hs, b, dk, n, k, j)) == 2520n : Nat}:
  match ok:
    case True{}:
      share_board(hs, Eq.cat(b, Comb.board(dk, n, k, j)), e2, e10)
    case False{}:
      Empty.absurd({Spec.share_sum(Eq.at.go(False{}, hs, b, dk, n, k, j)) == 2520n : Nat}, false_true(e))

def tcount_at.go(ok: Bool, e: {ok == True{} : Bool}, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +j: Nat) -> {Spec.tcount(Eq.at.go(ok, hs, b, dk, n, k, j)) == Spec.count(hs) : Nat}:
  match ok:
    case True{}:
      tcount_outcome(hs, Eq.cat(b, Comb.board(dk, n, k, j)))
    case False{}:
      Empty.absurd({Spec.tcount(Eq.at.go(False{}, hs, b, dk, n, k, j)) == Spec.count(hs) : Nat}, false_true(e))

def all_at.go(ok: Bool, e: {ok == True{} : Bool}, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +j: Nat) -> {Spec.all_sum(Eq.at.go(ok, hs, b, dk, n, k, j), 1n) == True{} : Bool}:
  match ok:
    case True{}:
      all_one_outcome(hs, Eq.cat(b, Comb.board(dk, n, k, j)))
    case False{}:
      Empty.absurd({Spec.all_sum(Eq.at.go(False{}, hs, b, dk, n, k, j), 1n) == True{} : Bool}, false_true(e))

def nil_at.go(ok: Bool, e: {ok == False{} : Bool}, -hs: List<&2, Spec.Hand>, -b: List<&2, Nat>, -dk: List<&2, Nat>, -n: Nat, -k: Nat, -j: Nat) -> {Eq.at.go(ok, hs, b, dk, n, k, j) == Nil{} : List<&2, Spec.Tally>}:
  match ok:
    case True{}:
      Empty.absurd({Eq.at.go(True{}, hs, b, dk, n, k, j) == Nil{} : List<&2, Spec.Tally>}, true_false(e))
    case False{}:
      {==}

# Past the last board, the loop tallies nothing.
def seq_nil(r: Nat, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +i: Nat, +e: {Nat.is_le(t, i) == True{} : Bool}) -> {Eq.seq(r, Eq.Ctx{hs, b, dk, n, k, t}, i) == Nil{} : List<&2, Spec.Tally>}:
  match r:
    case 0n:
      {==}
    case 1n++p:
      +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
      %Equal.sym(List<&2, Spec.Tally>, Eq.seq(p, x, i), Nil{}, seq_nil(p, hs, b, dk, n, k, t, i, e)) : {Eq.add(_, Eq.at(x, Nat.add(p, i))) == Nil{} : List<&2, Spec.Tally>}
      nil_at.go(Nat.is_lt(Nat.add(p, i), t), not_lt_of_le(t, Nat.add(p, i), le_add_l(p, t, i, e)), hs, b, dk, n, k, Nat.add(p, i))

def sub_add(a: Nat, b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case _ 0n:
      Equal.trans(Nat, Nat.add(Nat.sub(a, 0n), 0n), Nat.sub(a, 0n), a, add_zero(Nat.sub(a, 0n)), sub_zero_r(a))
    case 0n 1n+q:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, false_true(e))
    case 1n++p 1n++q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, add_succ(Nat.sub(p, q), q), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(p, q), q), p, sub_add(p, q, e)))

# A loop over P >= t boards tallies what the loop over the t boards tallies.
def seq_total(+hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +pp: Nat, e: {Nat.is_le(t, pp) == True{} : Bool}) -> {Eq.seq(pp, Eq.Ctx{hs, b, dk, n, k, t}, 0n) == Eq.seq(t, Eq.Ctx{hs, b, dk, n, k, t}, 0n) : List<&2, Spec.Tally>}:
  +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
  +r = Nat.sub(pp, t)
  +et = {(%Equal.sym(Nat, Nat.add(t, 0n), t, add_zero(t)) : {Nat.is_le(t, _) == True{} : Bool}; le_refl(t)) : {Nat.is_le(t, Nat.add(t, 0n)) == True{} : Bool}}
  %sub_add(pp, t, e) : {Eq.seq(_, x, 0n) == Eq.seq(t, x, 0n) : List<&2, Spec.Tally>}
  %seq_add(r, t, x, 0n) : {_ == Eq.seq(t, x, 0n) : List<&2, Spec.Tally>}
  %Equal.sym(List<&2, Spec.Tally>, Eq.seq(r, x, Nat.add(t, 0n)), Nil{}, seq_nil(r, hs, b, dk, n, k, t, Nat.add(t, 0n), et)) : {Eq.add(Eq.seq(t, x, 0n), _) == Eq.seq(t, x, 0n) : List<&2, Spec.Tally>}
  add_nil(Eq.seq(t, x, 0n))

def cong2_add(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def share_add(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>) -> {Spec.share_sum(Eq.add(a, b)) == Nat.add(Spec.share_sum(a), Spec.share_sum(b)) : Nat}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, xs} Nil{}:
      Equal.sym(Nat, Nat.add(Spec.share_sum(Con{x, xs}), 0n), Spec.share_sum(Con{x, xs}), add_zero(Spec.share_sum(Con{x, xs})))
    case Con{Spec.Tally{w1, t1, l1, +s1}, +xs} Con{Spec.Tally{w2, t2, l2, +s2}, +ys}:
      +sx = Spec.share_sum(xs)
      +sy = Spec.share_sum(ys)
      Equal.trans(Nat, Nat.add(Nat.add(s1, s2), Spec.share_sum(Eq.add(xs, ys))), Nat.add(Nat.add(s1, s2), Nat.add(sx, sy)), Nat.add(Nat.add(s1, sx), Nat.add(s2, sy)), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(s1, s2), z), Spec.share_sum(Eq.add(xs, ys)), Nat.add(sx, sy), share_add(xs, ys)), add4(s1, s2, sx, sy))

# The shares of the first m <= t boards add to 2520 each.
def share_seq(m: Nat, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +e: {Nat.is_le(m, t) == True{} : Bool}, +e2: {Nat.is_le(2n, Spec.count(hs)) == True{} : Bool}, +e10: {Nat.is_le(Spec.count(hs), 10n) == True{} : Bool}) -> {Spec.share_sum(Eq.seq(m, Eq.Ctx{hs, b, dk, n, k, t}, 0n)) == Nat.mul(m, 2520n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
      +j = Nat.add(p, 0n)
      +sa = Spec.share_sum(Eq.seq(p, x, 0n))
      +sb = Spec.share_sum(Eq.at(x, j))
      +mp = Nat.mul(p, 2520n)
      +lt = {(%Equal.sym(Nat, j, p, add_zero(p)) : {Nat.is_lt(_, t) == True{} : Bool}; le_succ_lt(p, t, e)) : {Nat.is_lt(j, t) == True{} : Bool}}
      +ea = share_seq(p, hs, b, dk, n, k, t, le_weaken(p, t, e), e2, e10)
      +eb = share_at.go(Nat.is_lt(j, t), lt, hs, b, dk, n, k, j, e2, e10)
      Equal.trans(Nat, Spec.share_sum(Eq.add(Eq.seq(p, x, 0n), Eq.at(x, j))), Nat.add(sa, sb), Nat.add(2520n, mp), share_add(Eq.seq(p, x, 0n), Eq.at(x, j)), Equal.trans(Nat, Nat.add(sa, sb), Nat.add(mp, 2520n), Nat.add(2520n, mp), cong2_add(sa, mp, sb, 2520n, ea, eb), add_comm(mp, 2520n)))

def max_self(a: Nat) -> {Nat.max(a, a) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.max(p, p), p, max_self(p))

def tcount_add_max(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>) -> {Spec.tcount(Eq.add(a, b)) == Nat.max(Spec.tcount(a), Spec.tcount(b)) : Nat}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{x, xs} Con{y, ys}:
      Equal.cong(Nat, Nat, z => 1n+z, Spec.tcount(Eq.add(xs, ys)), Nat.max(Spec.tcount(xs), Spec.tcount(ys)), tcount_add_max(xs, ys))

def tcount_add_eq(+a: List<&2, Spec.Tally>, +b: List<&2, Spec.Tally>, +c: Nat, ea: {Spec.tcount(a) == c : Nat}, eb: {Spec.tcount(b) == c : Nat}) -> {Spec.tcount(Eq.add(a, b)) == c : Nat}:
  Equal.trans(Nat, Spec.tcount(Eq.add(a, b)), Nat.max(Spec.tcount(a), Spec.tcount(b)), c, tcount_add_max(a, b), (%Equal.sym(Nat, Spec.tcount(a), c, ea) : {Nat.max(_, Spec.tcount(b)) == c : Nat}; %Equal.sym(Nat, Spec.tcount(b), c, eb) : {Nat.max(c, _) == c : Nat}; max_self(c)))

# The first p + 1 <= t boards give one tally per hand.
def tcount_seq1(p: Nat, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +e: {Nat.is_le(1n+p, t) == True{} : Bool}) -> {Spec.tcount(Eq.seq(1n+p, Eq.Ctx{hs, b, dk, n, k, t}, 0n)) == Spec.count(hs) : Nat}:
  match p:
    case 0n:
      tcount_at.go(Nat.is_lt(0n, t), le_succ_lt(0n, t, e), hs, b, dk, n, k, 0n)
    case 1n++q:
      +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
      +j = Nat.add(1n+q, 0n)
      +lt = {(%Equal.sym(Nat, j, 1n+q, add_zero(1n+q)) : {Nat.is_lt(_, t) == True{} : Bool}; le_succ_lt(1n+q, t, e)) : {Nat.is_lt(j, t) == True{} : Bool}}
      tcount_add_eq(Eq.seq(1n+q, x, 0n), Eq.at(x, j), Spec.count(hs), tcount_seq1(q, hs, b, dk, n, k, t, le_weaken(1n+q, t, e)), tcount_at.go(Nat.is_lt(j, t), lt, hs, b, dk, n, k, j))

# Two tally lists of one length, counting n1 and n2 boards, add to n1 + n2.
def all_sum_add(a: List<&2, Spec.Tally>, b: List<&2, Spec.Tally>, +n1: Nat, +n2: Nat, +ea: {Spec.all_sum(a, n1) == True{} : Bool}, +eb: {Spec.all_sum(b, n2) == True{} : Bool}, el: {Spec.tcount(a) == Spec.tcount(b) : Nat}) -> {Spec.all_sum(Eq.add(a, b), Nat.add(n1, n2)) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      Empty.absurd({Spec.all_sum(Eq.add(Nil{}, Con{y, ys}), Nat.add(n1, n2)) == True{} : Bool}, zero_succ(Spec.tcount(ys), el))
    case Con{x, xs} Nil{}:
      Empty.absurd({Spec.all_sum(Eq.add(Con{x, xs}, Nil{}), Nat.add(n1, n2)) == True{} : Bool}, zero_succ(Spec.tcount(xs), Equal.sym(Nat, 1n+Spec.tcount(xs), 0n, el)))
    case Con{Spec.Tally{+w1, +t1, +l1, s1}, +xs} Con{Spec.Tally{+w2, +t2, +l2, s2}, +ys}:
      +x1 = Nat.add(t1, l1)
      +x2 = Nat.add(t2, l2)
      +ca = Nat.is_eq(Nat.add(w1, x1), n1)
      +cb = Nat.is_eq(Nat.add(w2, x2), n2)
      +sa = eq_of_is_eq(Nat.add(w1, x1), n1, and_l(ca, Spec.all_sum(xs, n1), ea))
      +sb = eq_of_is_eq(Nat.add(w2, x2), n2, and_l(cb, Spec.all_sum(ys, n2), eb))
      +lhs = Nat.add(Nat.add(w1, w2), Nat.add(Nat.add(t1, t2), Nat.add(l1, l2)))
      +rhs = Nat.add(Nat.add(w1, x1), Nat.add(w2, x2))
      +rearr = Equal.trans(Nat, lhs, Nat.add(Nat.add(w1, w2), Nat.add(x1, x2)), rhs, Equal.cong(Nat, Nat, z => Nat.add(Nat.add(w1, w2), z), Nat.add(Nat.add(t1, t2), Nat.add(l1, l2)), Nat.add(x1, x2), add4(t1, t2, l1, l2)), add4(w1, w2, x1, x2))
      +field = {(%Equal.sym(Nat, lhs, rhs, rearr) : {Nat.is_eq(_, Nat.add(n1, n2)) == True{} : Bool}; %Equal.sym(Nat, Nat.add(w1, x1), n1, sa) : {Nat.is_eq(Nat.add(_, Nat.add(w2, x2)), Nat.add(n1, n2)) == True{} : Bool}; %Equal.sym(Nat, Nat.add(w2, x2), n2, sb) : {Nat.is_eq(Nat.add(n1, _), Nat.add(n1, n2)) == True{} : Bool}; eq_refl(Nat.add(n1, n2))) : {Nat.is_eq(lhs, Nat.add(n1, n2)) == True{} : Bool}}
      and_intro(Nat.is_eq(lhs, Nat.add(n1, n2)), Spec.all_sum(Eq.add(xs, ys), Nat.add(n1, n2)), field, all_sum_add(xs, ys, n1, n2, and_r(ca, Spec.all_sum(xs, n1), ea), and_r(cb, Spec.all_sum(ys, n2), eb), succ_inj(Spec.tcount(xs), Spec.tcount(ys), el)))

# The first p + 1 <= t boards are each counted once per hand.
def all_sum_seq1(p: Nat, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, +e: {Nat.is_le(1n+p, t) == True{} : Bool}) -> {Spec.all_sum(Eq.seq(1n+p, Eq.Ctx{hs, b, dk, n, k, t}, 0n), 1n+p) == True{} : Bool}:
  match p:
    case 0n:
      all_at.go(Nat.is_lt(0n, t), le_succ_lt(0n, t, e), hs, b, dk, n, k, 0n)
    case 1n++q:
      +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
      +j = Nat.add(1n+q, 0n)
      +lt = {(%Equal.sym(Nat, j, 1n+q, add_zero(1n+q)) : {Nat.is_lt(_, t) == True{} : Bool}; le_succ_lt(1n+q, t, e)) : {Nat.is_lt(j, t) == True{} : Bool}}
      +ew = le_weaken(1n+q, t, e)
      +el = Equal.trans(Nat, Spec.tcount(Eq.seq(1n+q, x, 0n)), Spec.count(hs), Spec.tcount(Eq.at(x, j)), tcount_seq1(q, hs, b, dk, n, k, t, ew), Equal.sym(Nat, Spec.tcount(Eq.at(x, j)), Spec.count(hs), tcount_at.go(Nat.is_lt(j, t), lt, hs, b, dk, n, k, j)))
      %add_one(q) : {Spec.all_sum(Eq.add(Eq.seq(1n+q, x, 0n), Eq.at(x, j)), 1n+_) == True{} : Bool}
      all_sum_add(Eq.seq(1n+q, x, 0n), Eq.at(x, j), 1n+q, 1n, all_sum_seq1(q, hs, b, dk, n, k, t, ew), all_at.go(Nat.is_lt(j, t), lt, hs, b, dk, n, k, j), el)

# The loop over the t >= 1 boards counts every board once for every hand.
def counted_seq(m: Nat, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, +dk: List<&2, Nat>, +n: Nat, +k: Nat, +t: Nat, e1: {Nat.is_le(1n, m) == True{} : Bool}, +e2: {Nat.is_le(m, t) == True{} : Bool}) -> {Spec.counted(Eq.seq(m, Eq.Ctx{hs, b, dk, n, k, t}, 0n), Spec.count(hs), m) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Spec.counted(Eq.seq(0n, Eq.Ctx{hs, b, dk, n, k, t}, 0n), Spec.count(hs), 0n) == True{} : Bool}, false_true(e1))
    case 1n++p:
      +x = {Eq.Ctx{hs, b, dk, n, k, t} : Eq.Ctx}
      +s = Eq.seq(1n+p, x, 0n)
      +ec = {(%Equal.sym(Nat, Spec.tcount(s), Spec.count(hs), tcount_seq1(p, hs, b, dk, n, k, t, e2)) : {Nat.is_eq(_, Spec.count(hs)) == True{} : Bool}; eq_refl(Spec.count(hs))) : {Nat.is_eq(Spec.tcount(s), Spec.count(hs)) == True{} : Bool}}
      and_intro(Nat.is_eq(Spec.tcount(s), Spec.count(hs)), Spec.all_sum(s, 1n+p), ec, all_sum_seq1(p, hs, b, dk, n, k, t, e2))

# The deck of a valid spot
# ------------------------

# How many of xs are below n.
def cnt_lt(xs: List<&2, Nat>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(Eq.b2n(Nat.is_lt(h, n)), cnt_lt(t, n))

def lt_zero(h: Nat) -> {Nat.is_lt(h, 0n) == False{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cnt_lt_zero(xs: List<&2, Nat>) -> {cnt_lt(xs, 0n) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(Bool, Nat.is_lt(h, 0n), False{}, lt_zero(h)) : {Nat.add(Eq.b2n(_), cnt_lt(t, 0n)) == 0n : Nat}
      cnt_lt_zero(t)

def cnt_lt_all(xs: List<&2, Nat>, +n: Nat, +e: {Spec.all_lt(xs, n) == True{} : Bool}) -> {cnt_lt(xs, n) == Spec.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Nat.is_lt(h, n), True{}, and_l(Nat.is_lt(h, n), Spec.all_lt(t, n), e)) : {Nat.add(Eq.b2n(_), cnt_lt(t, n)) == 1n+Spec.len(t) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, cnt_lt(t, n), Spec.len(t), cnt_lt_all(t, n, and_r(Nat.is_lt(h, n), Spec.all_lt(t, n), e)))

def lt_succ_split(h: Nat, p: Nat) -> {Eq.b2n(Nat.is_lt(h, 1n+p)) == Nat.add(Eq.b2n(Nat.is_lt(h, p)), Eq.b2n(Nat.is_eq(h, p))) : Nat}:
  match h p:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+r 0n:
      %Equal.sym(Bool, Nat.is_lt(r, 0n), False{}, lt_zero(r)) : {Eq.b2n(_) == 0n : Nat}
      {==}
    case 1n+r 1n+q:
      lt_succ_split(r, q)

def or_split(u: Bool, v: Bool, e: {(u && v) == False{} : Bool}) -> {Eq.b2n(u || v) == Nat.add(Eq.b2n(u), Eq.b2n(v)) : Nat}:
  match u v:
    case True{} True{}:
      Empty.absurd({Eq.b2n(True{} || True{}) == Nat.add(1n, 1n) : Nat}, true_false(e))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def not_inv(v: Bool, e: {Spec.not_(v) == True{} : Bool}) -> {v == False{} : Bool}:
  match v:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(e))
    case False{}:
      {==}

def no_both.go(u: Bool, +h: Nat, +p: Nat, +t: List<&2, Nat>, eu: {Nat.is_eq(h, p) == u : Bool}, eh: {Spec.has(t, h) == False{} : Bool}) -> {(u && Comb.mem(t, p)) == False{} : Bool}:
  match u:
    case False{}:
      {==}
    case True{}:
      %eq_of_is_eq(h, p, eu) : {Comb.mem(t, _) == False{} : Bool}
      %Equal.sym(Bool, Comb.mem(t, h), Spec.has(t, h), mem_has(t, h)) : {_ == False{} : Bool}
      eh

# A card of a list with no card twice is counted once below p + 1.
def cnt_lt_step(xs: List<&2, Nat>, +p: Nat, +e: {Spec.distinct(xs) == True{} : Bool}) -> {cnt_lt(xs, 1n+p) == Nat.add(cnt_lt(xs, p), Eq.b2n(Comb.mem(xs, p))) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +lt = Eq.b2n(Nat.is_lt(h, p))
      +eq = Eq.b2n(Nat.is_eq(h, p))
      +c = cnt_lt(t, p)
      +mt = Eq.b2n(Comb.mem(t, p))
      +et = and_r(Spec.not_(Spec.has(t, h)), Spec.distinct(t), e)
      +eh = not_inv(Spec.has(t, h), and_l(Spec.not_(Spec.has(t, h)), Spec.distinct(t), e))
      +nb = no_both.go(Nat.is_eq(h, p), h, p, t, {==}, eh)
      Equal.trans(Nat, Nat.add(Eq.b2n(Nat.is_lt(h, 1n+p)), cnt_lt(t, 1n+p)), Nat.add(Nat.add(lt, eq), Nat.add(c, mt)), Nat.add(Nat.add(lt, c), Eq.b2n(Nat.is_eq(h, p) || Comb.mem(t, p))), cong2_add(Eq.b2n(Nat.is_lt(h, 1n+p)), Nat.add(lt, eq), cnt_lt(t, 1n+p), Nat.add(c, mt), lt_succ_split(h, p), cnt_lt_step(t, p, et)), Equal.trans(Nat, Nat.add(Nat.add(lt, eq), Nat.add(c, mt)), Nat.add(Nat.add(lt, c), Nat.add(eq, mt)), Nat.add(Nat.add(lt, c), Eq.b2n(Nat.is_eq(h, p) || Comb.mem(t, p))), add4(lt, eq, c, mt), Equal.cong(Nat, Nat, z => Nat.add(Nat.add(lt, c), z), Nat.add(eq, mt), Eq.b2n(Nat.is_eq(h, p) || Comb.mem(t, p)), Equal.sym(Nat, Eq.b2n(Nat.is_eq(h, p) || Comb.mem(t, p)), Nat.add(eq, mt), or_split(Nat.is_eq(h, p), Comb.mem(t, p), nb)))))

def size_step(u: Bool, +g: Nat, +c: Nat, +p: Nat, ih: {Nat.add(g, c) == p : Nat}) -> {Nat.add(Nat.add(Comb.deck_size.one(u), g), Nat.add(c, Eq.b2n(u))) == 1n+p : Nat}:
  match u:
    case True{}:
      Equal.trans(Nat, Nat.add(g, Nat.add(c, 1n)), Nat.add(Nat.add(g, c), 1n), 1n+p, add_assoc(g, c, 1n), Equal.trans(Nat, Nat.add(Nat.add(g, c), 1n), Nat.add(p, 1n), 1n+p, Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(g, c), p, ih), add_one(p)))
    case False{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(g, Nat.add(c, 0n)), p, Equal.trans(Nat, Nat.add(g, Nat.add(c, 0n)), Nat.add(g, c), p, Equal.cong(Nat, Nat, z => Nat.add(g, z), Nat.add(c, 0n), c, add_zero(c)), ih))

# The cards below n not in K, plus those in K, are the n cards below n.
def size_go_cnt(n: Nat, +xs: List<&2, Nat>, +e: {Spec.distinct(xs) == True{} : Bool}) -> {Nat.add(Comb.deck_size.go(n, xs), cnt_lt(xs, n)) == n : Nat}:
  match n:
    case 0n:
      cnt_lt_zero(xs)
    case 1n++p:
      %Equal.sym(Nat, cnt_lt(xs, 1n+p), Nat.add(cnt_lt(xs, p), Eq.b2n(Comb.mem(xs, p))), cnt_lt_step(xs, p, e)) : {Nat.add(Nat.add(Comb.deck_size.one(Comb.mem(xs, p)), Comb.deck_size.go(p, xs)), _) == 1n+p : Nat}
      size_step(Comb.mem(xs, p), Comb.deck_size.go(p, xs), cnt_lt(xs, p), p, size_go_cnt(p, xs, e))

# Real cards, none twice: the deck holds the other 52 - |K|.
def deck_size_eq(+xs: List<&2, Nat>, ed: {Spec.distinct(xs) == True{} : Bool}, el: {Spec.all_lt(xs, 52n) == True{} : Bool}) -> {Comb.deck_size(xs) == Nat.sub(52n, Spec.len(xs)) : Nat}:
  sub_of_add(Comb.deck_size(xs), Spec.len(xs), 52n, (%cnt_lt_all(xs, 52n, el) : {Nat.add(Comb.deck_size(xs), _) == 52n : Nat}; size_go_cnt(52n, xs, ed)))

# Counts
# ------

def dm_ge(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.is_le(d, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(d)
    case 1n++np:
      match m:
        case 0n:
          le_weaken(d, Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), dm_ge(np, r, 1n+d, 0n))
        case 1n+mp:
          dm_ge(np, mp, d, 1n+r)

def dm_pos(n: Nat, m: Nat, +d: Nat, +r: Nat, e: {Nat.is_le(1n+m, n) == True{} : Bool}) -> {Nat.is_le(1n+d, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) == True{} : Bool}:
  match n m:
    case 0n _:
      Empty.absurd({Nat.is_le(1n+d, Pair.fst(Nat, Nat, Nat.divmod.go(0n, m, d, r))) == True{} : Bool}, false_true(e))
    case 1n+np 0n:
      dm_ge(np, r, 1n+d, 0n)
    case 1n+np 1n+mp:
      dm_pos(np, mp, d, 1n+r, e)

def mul_ge(a: Nat, +b: Nat, +e: {Nat.is_le(1n, b) == True{} : Bool}) -> {Nat.is_le(a, Nat.mul(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      le_add_mono(1n, p, b, Nat.mul(p, b), e, mul_ge(p, b, e))

# C(n, k) >= 1 for k <= n.
def binom_pos(n: Nat, k: Nat, +e: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.is_le(1n, Comb.binom(n, k)) == True{} : Bool}:
  match n k:
    case 0n 0n:
      {==}
    case 1n+m 0n:
      {==}
    case 0n 1n+j:
      Empty.absurd({Nat.is_le(1n, Comb.binom(0n, 1n+j)) == True{} : Bool}, false_true(e))
    case 1n++m 1n++j:
      +bb = Comb.binom(m, j)
      +a = Nat.mul(1n+m, bb)
      dm_pos(a, j, 0n, 0n, le_trans(1n+j, 1n+m, a, e, mul_ge(1n+m, bb, binom_pos(m, j, e))))

def len_cards(hs: List<&2, Spec.Hand>, +b: List<&2, Nat>) -> {Spec.len(Spec.cards(hs, b)) == Nat.add(Nat.double(Spec.count(hs)), Spec.len(b)) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{Spec.Hand{x, y}, t}:
      Equal.cong(Nat, Nat, z => 2n+z, Spec.len(Spec.cards(t, b)), Nat.add(Nat.double(Spec.count(t)), Spec.len(b)), len_cards(t, b))

def dbl_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  match a b:
    case 0n _:
      le_zero(Nat.double(b))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.double(1n+p), 0n) == True{} : Bool}, false_true(e))
    case 1n+p 1n+q:
      dbl_le(p, q, e)

def bso_le5(m: Nat, e: {Spec.board_size_ok(m) == True{} : Bool}) -> {Nat.is_le(m, 5n) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+m1:
      match m1:
        case 0n:
          {==}
        case 1n+m2:
          match m2:
            case 0n:
              {==}
            case 1n+m3:
              match m3:
                case 0n:
                  {==}
                case 1n+m4:
                  match m4:
                    case 0n:
                      {==}
                    case 1n+m5:
                      match m5:
                        case 0n:
                          {==}
                        case 1n+m6:
                          Empty.absurd({Nat.is_le(6n+m6, 5n) == True{} : Bool}, false_true(e))

# A valid spot leaves at least as many cards as the board still needs.
def k_le_n(+c: Nat, +l: Nat, ec: {Nat.is_le(c, 10n) == True{} : Bool}, eb: {Spec.board_size_ok(l) == True{} : Bool}) -> {Nat.is_le(Nat.sub(5n, l), Nat.sub(52n, Nat.add(Nat.double(c), l))) == True{} : Bool}:
  +x = Nat.add(Nat.double(c), l)
  le_trans(Nat.sub(5n, l), 5n, Nat.sub(52n, x), sub_le(5n, l), le_trans(5n, Nat.sub(52n, 25n), Nat.sub(52n, x), {==}, sub_anti(x, 25n, 52n, le_add_mono(Nat.double(c), l, 20n, 5n, dbl_le(c, 10n, ec), bso_le5(l, eb)))))

# The two laws
# ------------

# run on a spot is the loop over its boards: its tree, by LAW 1, is the loop
# over 2^clog2(t) >= t boards, and the boards past t tally nothing.
def run_cpu_seq(+hs: List<&2, Spec.Hand>, +b: List<&2, Nat>) -> {Eq.run.cpu(Eq.ctx(Spec.Spot{hs, b})) == Eq.seq(Comb.binom(Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b))), Eq.Ctx{hs, b, Comb.deck(Spec.cards(hs, b)), Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b)))}, 0n) : List<&2, Spec.Tally>}:
  +kn = Spec.cards(hs, b)
  +n = Comb.deck_size(kn)
  +k = Nat.sub(5n, Spec.len(b))
  +t = Comb.binom(n, k)
  +x = {Eq.Ctx{hs, b, Comb.deck(kn), n, k, t} : Eq.Ctx}
  +dd = Comb.clog2(t)
  +d = Nat.min(dd, 14n)
  +c = Nat.sub(dd, d)
  Equal.trans(List<&2, Spec.Tally>, Eq.tree(d, c, x, 0n), Eq.seq(Comb.pow2(Nat.add(d, c)), x, 0n), Eq.seq(t, x, 0n), Laws.tree_is_seq(d, c, x, 0n), (%Equal.sym(Nat, Nat.add(d, c), dd, min_sub(dd, 14n)) : {Eq.seq(Comb.pow2(_), x, 0n) == Eq.seq(t, x, 0n) : List<&2, Spec.Tally>}; seq_total(hs, b, Comb.deck(kn), n, k, t, Comb.pow2(dd), clog2_ge(t))))

# The GPU and the CPU run the same tree (`tree!` is `tree`).
def run_seq(g: Bool, +hs: List<&2, Spec.Hand>, +b: List<&2, Nat>) -> {Eq.run(g, Spec.Spot{hs, b}) == Eq.seq(Comb.binom(Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b))), Eq.Ctx{hs, b, Comb.deck(Spec.cards(hs, b)), Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b)), Comb.binom(Comb.deck_size(Spec.cards(hs, b)), Nat.sub(5n, Spec.len(b)))}, 0n) : List<&2, Spec.Tally>}:
  match g:
    case True{}:
      run_cpu_seq(hs, b)
    case False{}:
      run_cpu_seq(hs, b)

# LAW 5's claim, with ok live.
def tally_total_live(+g: Bool, s: Spec.Spot, +ok: {Spec.valid(s) == True{} : Bool}) -> {Spec.counted(Eq.run(g, s), Spec.players(s), Spec.boards(s)) == True{} : Bool}:
  match s:
    case Spec.Spot{+hs, +b}:
      +kn = Spec.cards(hs, b)
      +c = Spec.count(hs)
      +l = Spec.len(b)
      +k = Nat.sub(5n, l)
      +n = Comb.deck_size(kn)
      +t = Comb.binom(n, k)
      +x = {Eq.Ctx{hs, b, Comb.deck(kn), n, k, t} : Eq.Ctx}
      +va = Nat.is_le(2n, c)
      +vb = Nat.is_le(c, 10n)
      +vc = Spec.board_size_ok(l)
      +vd = Spec.all_lt(kn, 52n)
      +ve = Spec.distinct(kn)
      +eabcd = and_l(((va && vb) && vc) && vd, ve, ok)
      +ee = and_r(((va && vb) && vc) && vd, ve, ok)
      +eabc = and_l((va && vb) && vc, vd, eabcd)
      +ed = and_r((va && vb) && vc, vd, eabcd)
      +eab = and_l(va && vb, vc, eabc)
      +ec = and_r(va && vb, vc, eabc)
      +eb = and_r(va, vb, eab)
      +dse = deck_size_eq(kn, ee, ed)
      +kle = {(%Equal.sym(Nat, n, Nat.sub(52n, Spec.len(kn)), dse) : {Nat.is_le(k, _) == True{} : Bool}; %Equal.sym(Nat, Spec.len(kn), Nat.add(Nat.double(c), l), len_cards(hs, b)) : {Nat.is_le(k, Nat.sub(52n, _)) == True{} : Bool}; k_le_n(c, l, eb, ec)) : {Nat.is_le(k, n) == True{} : Bool}}
      %Equal.sym(List<&2, Spec.Tally>, Eq.run(g, Spec.Spot{hs, b}), Eq.seq(t, x, 0n), run_seq(g, hs, b)) : {Spec.counted(_, c, Comb.binom(Nat.sub(52n, Spec.len(kn)), k)) == True{} : Bool}
      %dse : {Spec.counted(Eq.seq(t, x, 0n), c, Comb.binom(_, k)) == True{} : Bool}
      counted_seq(t, hs, b, Comb.deck(kn), n, k, t, binom_pos(n, k, kle), le_refl(t))

# LAW 6's claim, with ok live.
def share_total_live(+g: Bool, s: Spec.Spot, +ok: {Spec.valid(s) == True{} : Bool}) -> {Spec.share_sum(Eq.run(g, s)) == Nat.mul(2520n, Spec.boards(s)) : Nat}:
  match s:
    case Spec.Spot{+hs, +b}:
      +kn = Spec.cards(hs, b)
      +c = Spec.count(hs)
      +l = Spec.len(b)
      +k = Nat.sub(5n, l)
      +n = Comb.deck_size(kn)
      +t = Comb.binom(n, k)
      +x = {Eq.Ctx{hs, b, Comb.deck(kn), n, k, t} : Eq.Ctx}
      +va = Nat.is_le(2n, c)
      +vb = Nat.is_le(c, 10n)
      +vc = Spec.board_size_ok(l)
      +vd = Spec.all_lt(kn, 52n)
      +ve = Spec.distinct(kn)
      +eabcd = and_l(((va && vb) && vc) && vd, ve, ok)
      +ee = and_r(((va && vb) && vc) && vd, ve, ok)
      +eabc = and_l((va && vb) && vc, vd, eabcd)
      +ed = and_r((va && vb) && vc, vd, eabcd)
      +eab = and_l(va && vb, vc, eabc)
      +dse = deck_size_eq(kn, ee, ed)
      %Equal.sym(List<&2, Spec.Tally>, Eq.run(g, Spec.Spot{hs, b}), Eq.seq(t, x, 0n), run_seq(g, hs, b)) : {Spec.share_sum(_) == Nat.mul(2520n, Comb.binom(Nat.sub(52n, Spec.len(kn)), k)) : Nat}
      %dse : {Spec.share_sum(Eq.seq(t, x, 0n)) == Nat.mul(2520n, Comb.binom(_, k)) : Nat}
      Equal.trans(Nat, Spec.share_sum(Eq.seq(t, x, 0n)), Nat.mul(t, 2520n), Nat.mul(2520n, t), share_seq(t, hs, b, Comb.deck(kn), n, k, t, le_refl(t), and_l(va, vb, eab), and_r(va, vb, eab)), mul_comm(t, 2520n))

def Laws.tally_total(g, s, ok):
  tally_total_live(g, s, ok)
