#!/bin/sh
# Commit gate: every law proven, then the native build and one smoke spot.
set -eu
cd "$(dirname "$0")"
out=$(bend PROOF.bend 2>&1) || true
printf '%s\n' "$out"
case $out in
  *"SOME PROOFS FAIL"*) echo "check: proofs fail" >&2; exit 1 ;;
  *"ALL PROOFS CHECK"*) ;;
  *) echo "check: no proof verdict" >&2; exit 1 ;;
esac
mkdir -p bin
bend main.bend -o bin/bend-equity
./bin/bend-equity spot AsAh,KdKc Qs7h2c3d9s
