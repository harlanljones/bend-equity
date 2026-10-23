# main.bend: the bend-equity CLI.
#   bend-equity spot <hands> [<board>]   one spot, as one JSON line
#   bend-equity batch <file>             one JSON line per "<id> <hands> <board>" line
#   bend-equity certify                  the evaluator over all 7-card hands
# Every equity number comes from Eq.run.
import Base
import ./spec.bend as Spec
import ./comb.bend as Comb
import ./eval.bend as Eval
import ./equity.bend as Eq
import ./cards.bend as Cards
import ./certify.bend as Cert

type Parsed is Data:
  Good{s: Spec.Spot}
  Bad{code: String}

# JSON
# ----

def json_tally(t: Spec.Tally) -> String:
  match t:
    case Spec.Tally{w, ti, l, s}:
      "{\"win\":" ++ Nat.show(w) ++ ",\"tie\":" ++ Nat.show(ti) ++ ",\"lose\":" ++ Nat.show(l) ++ ",\"share\":" ++ Nat.show(s) ++ "}"

def json_tallies(ts: List<&2, Spec.Tally>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, Nil{}}:
      json_tally(t)
    case Con{t, rest}:
      json_tally(t) ++ "," ++ json_tallies(rest)

def json_nats(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      Nat.show(x)
    case Con{x, rest}:
      Nat.show(x) ++ "," ++ json_nats(rest)

def json_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def json_error(id: String, code: String) -> String:
  "{\"id\":\"" ++ id ++ "\",\"error\":\"" ++ code ++ "\"}"

# The spot's equity, from Eq.run.
def json_spot(id: String, +s: Spec.Spot) -> String:
  "{\"id\":\"" ++ id ++ "\",\"boards\":" ++ Nat.show(Spec.boards(s)) ++ ",\"players\":[" ++ json_tallies(Eq.run(Eq.gpu_worth(s), s)) ++ "]}"

def json_parsed(id: String, p: Parsed) -> String:
  match p:
    case Good{s}:
      json_spot(id, s)
    case Bad{code}:
      json_error(id, code)

# Parsing
# -------

def hand_of(m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, Spec.Hand>:
  match m:
    case Some{Con{x, Con{y, Nil{}}}}:
      Some{Spec.Hand{x, y}}
    case _:
      None{}

def hands(ts: List<&2, String>) -> Maybe<&2, List<&2, Spec.Hand>>:
  match ts:
    case Nil{}:
      Some{Nil{}}
    case Con{t, rest}:
      do Maybe<&2, List<&2, Spec.Hand>>:
        h : Spec.Hand <- hand_of(Cards.run(t))
        hs : List<&2, Spec.Hand> <- hands(rest)
        return h <> hs

def board_of(dash: Bool, t: String) -> Maybe<&2, List<&2, Nat>>:
  match dash:
    case True{}:
      Some{Nil{}}
    case False{}:
      Cards.run(t)

def board(+t: String) -> Maybe<&2, List<&2, Nat>>:
  board_of(String.eq(t, "-"), t)

def check.dup(hs: List<&2, Spec.Hand>, b: List<&2, Nat>, ok: Bool) -> Parsed:
  match ok:
    case True{}:
      Good{Spec.Spot{hs, b}}
    case False{}:
      Bad{"duplicate_card"}

def check.size(+hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, ok: Bool) -> Parsed:
  match ok:
    case True{}:
      check.dup(hs, b, Spec.distinct(Spec.cards(hs, b)))
    case False{}:
      Bad{"board_size"}

def check.players(+hs: List<&2, Spec.Hand>, +b: List<&2, Nat>, ok: Bool) -> Parsed:
  match ok:
    case True{}:
      check.size(hs, b, Spec.board_size_ok(Spec.len(b)))
    case False{}:
      Bad{"player_count"}

def check(hs: Maybe<&2, List<&2, Spec.Hand>>, b: Maybe<&2, List<&2, Nat>>) -> Parsed:
  match hs b:
    case Some{+h} Some{b}:
      +n = Spec.count(h)
      check.players(h, b, Nat.is_le(2n, n) && Nat.is_le(n, 10n))
    case _ _:
      Bad{"bad_card"}

# Error codes in order: bad_card, player_count, board_size, duplicate_card.
# A spot that passes them all is Spec.valid.
def parse(hs: String, b: String) -> Parsed:
  check(hands(String.split(hs, ',')), board(b))

# Batch lines
# -----------

def id_char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Char.is_alpha(Chr{x}) || Char.is_digit(Chr{x}) || U32.is_eq(x, 95) || U32.is_eq(x, 58) || U32.is_eq(x, 46) || U32.is_eq(x, 45)

def id_chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      id_char(c) && id_chars(t)

# [A-Za-z0-9_:.-]+
def id_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      id_char(c) && id_chars(t)

def line_id.of(id: String, ok: Bool) -> String:
  match ok:
    case True{}:
      id
    case False{}:
      "-"

def line_id(+id: String) -> String:
  line_id.of(id, id_ok(id))

def line.fields(+id: String, hs: String, b: String, ok: Bool) -> String:
  match ok:
    case True{}:
      json_parsed(id, parse(hs, b))
    case False{}:
      json_error("-", "bad_line")

def line(fs: List<&2, String>) -> String:
  match fs:
    case Con{+id, Con{hs, Con{b, Nil{}}}}:
      line.fields(id, hs, b, id_ok(id))
    case Con{+id, rest}:
      json_error(line_id(id), "bad_line")
    case Nil{}:
      json_error("-", "bad_line")

# One output line per non-empty input line.
def lines(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{SNil{}, rest}:
      lines(rest)
    case Con{l, rest}:
      line(String.split(l, ' ')) <> lines(rest)

# Effects
# -------

def usage() -> IO(Unit):
  do IO<Unit>:
    IO.print_err("usage: bend-equity spot <hands> [<board>] | batch <file> | certify")
    IO.exit(2)

def spot.out(p: Parsed) -> IO(Unit):
  match p:
    case Good{s}:
      IO.print(json_spot("-", s))
    case Bad{code}:
      do IO<Unit>:
        IO.print(json_error("-", code))
        IO.exit(2)

def spot(args: List<String>) -> IO(Unit):
  match args:
    case Con{hs, Nil{}}:
      spot.out(parse(hs, "-"))
    case Con{hs, Con{b, Nil{}}}:
      spot.out(parse(hs, b))
    case _:
      usage()

def read.step(r: File & Result<&1, &1, U32 & String, String>, acc: List<&2, String>, more: File -> List<&2, String> -> IO(Maybe<&2, String>)) -> IO(Maybe<&2, String>):
  (f, res) = r
  match res:
    case Fail{e}:
      do IO<Maybe<&2, String>>:
        File.close(f)
        return None{}
    case Done{SNil{}}:
      do IO<Maybe<&2, String>>:
        File.close(f)
        return Some{String.concat(List.reverse(&2, String, acc))}
    case Done{chunk}:
      more(f, chunk <> acc)

# The whole file, 64 KiB at a time (at most 16384 chunks).
def read.go(fuel: Nat, f: File, acc: List<&2, String>) -> IO(Maybe<&2, String>):
  match fuel:
    case 0n:
      do IO<Maybe<&2, String>>:
        File.close(f)
        return None{}
    case 1n+g:
      do IO<Maybe<&2, String>>:
        r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 65536)
        read.step(r, acc, f2 => acc2 => read.go(g, f2, acc2))

def read.opened(r: Result<&1, &1, U32 & String, File>) -> IO(Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, None{})
    case Done{f}:
      read.go(16384n, f, Nil{})

def batch.out(text: Maybe<&2, String>) -> IO(Unit):
  match text:
    case None{}:
      do IO<Unit>:
        IO.print("{\"error\":\"cannot_read\"}")
        IO.exit(2)
    case Some{t}:
      List.for_each(~&2, ~String, ~IO.print, lines(String.lines(t)))

def batch(args: List<String>) -> IO(Unit):
  match args:
    case Con{path, Nil{}}:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        text : Maybe<&2, String> <- read.opened(r)
        batch.out(text)
    case _:
      usage()

def same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      Nat.is_eq(x, y) && same(xs, ys)
    case _ _:
      False{}

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      Nat.add(x, sum(rest))

def certify.out(text: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.print(text)
    case False{}:
      do IO<Unit>:
        IO.print(text)
        IO.exit(1)

def certify(+hs: List<&2, Nat>) -> IO(Unit):
  +n = sum(hs)
  +ok = Nat.is_eq(n, Cert.hands()) && same(hs, Cert.expected())
  certify.out("{\"hands\":" ++ Nat.show(n) ++ ",\"categories\":[" ++ json_nats(hs) ++ "],\"ok\":" ++ json_bool(ok) ++ "}", ok)

def route(args: List<String>, is_spot: Bool, is_batch: Bool, is_cert: Bool) -> IO(Unit):
  match is_spot is_batch is_cert:
    case True{} _ _:
      spot(args)
    case False{} True{} _:
      batch(args)
    case False{} False{} True{}:
      certify(Cert.hist())
    case _ _ _:
      usage()

def dispatch(args: List<String>) -> IO(Unit):
  match args:
    case Con{prog, Con{+cmd, rest}}:
      route(rest, String.eq(cmd, "spot"), String.eq(cmd, "batch"), String.eq(cmd, "certify"))
    case _:
      usage()

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    dispatch(args)
