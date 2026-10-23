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
