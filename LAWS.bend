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
