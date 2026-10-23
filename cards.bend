# cards.bend: card text. A card is two characters, rank then suit
# ("23456789TJQKA", "cdhs"); its number is rank * 4 + suit.
import Base

def rank(c: Char) -> Maybe<&2, Nat>:
  match c:
    case '2':
      Some{0n}
    case '3':
      Some{1n}
    case '4':
      Some{2n}
    case '5':
      Some{3n}
    case '6':
      Some{4n}
    case '7':
      Some{5n}
    case '8':
      Some{6n}
    case '9':
      Some{7n}
    case 'T':
      Some{8n}
    case 'J':
      Some{9n}
    case 'Q':
      Some{10n}
    case 'K':
      Some{11n}
    case 'A':
      Some{12n}
    case _:
      None{}

def suit(c: Char) -> Maybe<&2, Nat>:
  match c:
    case 'c':
      Some{0n}
    case 'd':
      Some{1n}
    case 'h':
      Some{2n}
    case 's':
      Some{3n}
    case _:
      None{}

def join(r: Maybe<&2, Nat>, s: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r s:
    case Some{a} Some{b}:
      Some{Nat.add(Nat.mul(a, 4n), b)}
    case _ _:
      None{}

# A two-character card.
def parse(+t: String) -> Maybe<&2, Nat>:
  match t:
    case SCon{r, SCon{s, SNil{}}}:
      join(rank(r), suit(s))
    case _:
      None{}

def show(+c: Nat) -> String:
  +r = Maybe.default(&2, Char, String.get("23456789TJQKA", Nat.div(c, 4n)), '?')
  +s = Maybe.default(&2, Char, String.get("cdhs", Nat.mod(c, 4n)), '?')
  SCon{r, SCon{s, SNil{}}}

# A run of concatenated cards ("Qd7c2s"), in order.
def run(t: String) -> Maybe<&2, List<&2, Nat>>:
  match t:
    case SNil{}:
      Some{Nil{}}
    case SCon{r, SCon{s, rest}}:
      do Maybe<&2, List<&2, Nat>>:
        c : Nat <- join(rank(r), suit(s))
        cs : List<&2, Nat> <- run(rest)
        return c <> cs
    case _:
      None{}
