# bend-equity laws. Human-owned: agents never edit this file.
import Base
import ./spec.bend as Spec
import ./comb.bend as Comb
import ./equity.bend as Eq

# LAW 1: parallelism is safe: the fork/join tree of depth d with leaves of 2^c
# boards tallies exactly what the sequential loop over 2^(d+c) boards tallies.
law tree_is_seq:
  for +d: Nat
  for +c: Nat
  for +x: Eq.Ctx
  for +i: Nat
  {Eq.tree(d, c, x, i) == Eq.seq(Comb.pow2(Nat.add(d, c)), x, i) : List<&2, Spec.Tally>}

# LAW 2: every enumerated board is strictly ascending (no card twice) and uses real cards only.
law board_well_formed:
  for +known: List<&2, Nat>
  for +k: Nat
  for +i: Nat
  {Spec.well_formed(Comb.board(Comb.deck(known), Comb.deck_size(known), k, i)) == True{} : Bool}

# LAW 3: no enumerated board contains a known card (a hole card or a dealt board card).
law board_avoids_known:
  for +known: List<&2, Nat>
  for +k: Nat
  for +i: Nat
  for +c: Nat
  {(Spec.has(Comb.board(Comb.deck(known), Comb.deck_size(known), k, i), c) && Spec.has(known, c)) == False{} : Bool}

# LAW 4: seat order is irrelevant: swapping two players swaps their tallies, nothing else changes.
law heads_up_swap:
  for +g: Bool
  for +p: Spec.Hand
  for +q: Spec.Hand
  for +b: List<&2, Nat>
  {Eq.run(g, Spec.heads_up(q, p, b)) == Spec.swap2(Eq.run(g, Spec.heads_up(p, q, b))) : List<&2, Spec.Tally>}

# LAW 5: every board is counted exactly once for every player: win + tie + lose == boards.
law tally_total:
  for +g: Bool
  for +s: Spec.Spot
  for ok: {Spec.valid(s) == True{} : Bool}
  {Spec.counted(Eq.run(g, s), Spec.players(s), Spec.boards(s)) == True{} : Bool}
