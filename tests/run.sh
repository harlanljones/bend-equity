#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
./check.sh
./bin/bend-equity certify
uv run --with pokerkit==0.7.6 python tests/pokerkit_diff.py --bin bin/bend-equity
bend PROOF.bend --verdict
