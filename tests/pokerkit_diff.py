"""Differential test: bend-equity against PokerKit 0.7.6.

Exact spots (river, turn, flop, two fixed) are enumerated here board by board
with StandardHighHand and must match the CLI's integers exactly. Preflop spots
are compared with PokerKit's Monte Carlo calculate_equities within 1 point.

    uv run --with pokerkit==0.7.6 python tests/pokerkit_diff.py --bin bin/bend-equity
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

from pokerkit import Deck, StandardHighHand, calculate_equities, parse_range

RANKS = "23456789TJQKA"
SUITS = "cdhs"
DECK = [f"{r}{s}" for r in RANKS for s in SUITS]
SHARE_UNIT = 2520
PREFLOP_SAMPLES = 50000
PREFLOP_TOLERANCE = 1.0  # percentage points per player

FIXED = [("AsAh", "KdKc"), ("AsKd", "AhKc")]
FIXED_BOARDS = ["Qs7h2c3d9s", "QsJh2c3d9s"]
PREFLOP = [("AsAh", "KdKc"), ("AhKh", "QsQd"), ("7c2d", "AsKs")]


def deal(rng: random.Random, players: int, board: int) -> tuple[list[str], list[str]]:
    cards = rng.sample(DECK, 2 * players + board)
    holes = [cards[2 * i] + cards[2 * i + 1] for i in range(players)]
    return holes, cards[2 * players :]


def spots(rng: random.Random) -> list[tuple[str, list[str], list[str]]]:
    out: list[tuple[str, list[str], list[str]]] = []
    for name, count, board, lo, hi in (
        ("river", 60, 5, 2, 10),
        ("turn", 40, 4, 2, 6),
        ("flop", 30, 3, 2, 4),
    ):
        for i in range(count):
            holes, cards = deal(rng, rng.randint(lo, hi), board)
            out.append((f"{name}-{i:02d}", holes, cards))
    for i, (holes, board) in enumerate(zip(FIXED, FIXED_BOARDS, strict=True)):
        out.append((f"fixed-{i}", list(holes), [board[j : j + 2] for j in range(0, 10, 2)]))
    return out


def exact(holes: list[str], board: list[str]) -> dict:
    known = set(board) | {h[i : i + 2] for h in holes for i in (0, 2)}
    rest = sorted(c for c in DECK if c not in known)
    n = len(holes)
    tallies = [{"win": 0, "tie": 0, "lose": 0, "share": 0} for _ in range(n)]
    boards = 0
    for combo in itertools.combinations(rest, 5 - len(board)):
        full = "".join(board) + "".join(combo)
        hands = [StandardHighHand.from_game(h, full) for h in holes]
        best = max(hands)
        winners = [i for i, h in enumerate(hands) if h == best]
        share = SHARE_UNIT // len(winners)
        for i in range(n):
            if i not in winners:
                tallies[i]["lose"] += 1
            else:
                tallies[i]["win" if len(winners) == 1 else "tie"] += 1
                tallies[i]["share"] += share
        boards += 1
    return {"boards": boards, "players": tallies}


def preflop_mc(holes: tuple[str, str]) -> list[float]:
    ranges = tuple(parse_range(h) for h in holes)
    eq = calculate_equities(
        ranges,
        (),
        2,
        5,
        Deck.STANDARD,
        (StandardHighHand,),
        sample_count=PREFLOP_SAMPLES,
    )
    return [100 * e for e in eq]


def run_batch(binary: str, lines: list[str]) -> dict[str, dict]:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "spots.txt"
        path.write_text("".join(f"{line}\n" for line in lines))
        proc = subprocess.run(
            [binary, "batch", str(path)], capture_output=True, text=True, check=False
        )
    if proc.returncode != 0:
        sys.exit(f"batch exited {proc.returncode}: {proc.stderr.strip() or proc.stdout.strip()}")
    results = [json.loads(line) for line in proc.stdout.splitlines() if line.strip()]
    return {r["id"]: r for r in results}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, help="path to the bend-equity binary")
    args = ap.parse_args()

    rng = random.Random(20261023)
    cases = spots(rng)
    lines = [f"{sid} {','.join(holes)} {''.join(board) or '-'}" for sid, holes, board in cases]
    lines += [f"pre-{i} {','.join(h)} -" for i, h in enumerate(PREFLOP)]
    got = run_batch(args.bin, lines)

    failed: list[str] = []
    for sid, holes, board in cases:
        want = exact(holes, board)
        have = got.get(sid)
        if have is None or have.get("boards") != want["boards"] or have.get("players") != want["players"]:
            failed.append(sid)
            print(f"MISMATCH {sid}: want {json.dumps(want)} got {json.dumps(have)}", file=sys.stderr)
    exact_ok = len(cases) - len(failed)

    mc_ok = 0
    for i, holes in enumerate(PREFLOP):
        sid = f"pre-{i}"
        have = got.get(sid)
        want = preflop_mc(holes)
        if have is None or "players" not in have:
            failed.append(sid)
            print(f"MISMATCH {sid}: no result {json.dumps(have)}", file=sys.stderr)
            continue
        pcts = [100 * p["share"] / (SHARE_UNIT * have["boards"]) for p in have["players"]]
        if all(abs(a - b) <= PREFLOP_TOLERANCE for a, b in zip(pcts, want, strict=True)):
            mc_ok += 1
        else:
            failed.append(sid)
            print(f"MISMATCH {sid}: bend {pcts} pokerkit {want}", file=sys.stderr)

    print(f"exact {exact_ok}/{len(cases)}, preflop-mc {mc_ok}/{len(PREFLOP)}")
    if failed:
        print("failed: " + " ".join(failed), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
