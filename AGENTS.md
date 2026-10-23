# bend-equity — agent rules

When using Bend:
- run `bend guide` to learn it
- use `LAWS.bend` to keep important rules
- run `bend PROOF.bend` before committing
- parallelize the code whenever possible

Project rules:
- `LAWS.bend` and `spec.bend` are human-owned: their text comes verbatim from the approved plan.
  Never alter, weaken, or delete a law statement or a spec definition. A law that looks wrong or
  unprovable is reported to the human, never rewritten.
- Every equity number the CLI prints comes from `Eq.run`; never compute equity another way.
- No `@unsafe`, no `f?`, no foreign effects in spec.bend, comb.bend, eval.bend, equity.bend.
- Before every commit run `./check.sh`; it must print ALL PROOFS CHECK and exit 0.
- After any change to comb.bend, eval.bend, equity.bend or main.bend also run `./tests/run.sh`.
- Commits: Conventional Commits (`feat|fix|chore|docs|refactor|test[(scope)]: subject`).
