# allones-comparator

Palomar comparator: Gallardo's 2019 conjecture on OEIS A071642, resolved and machine-checked in
Lean 4. For every `n ≥ 2`, the all-ones polynomial `1 + X + ⋯ + Xⁿ` is irreducible over `GF(2)` if
and only if `1 + P + ⋯ + Pⁿ` is, where `P = X² + X + 1` (TheoremDB P12771).

- `Challenge.lean` — the statement surface (imports only Mathlib).
- `Solution.lean` — the same declarations, discharged from the `AllOnesLab` library.
- `AllOnesLab/` — the proof development (`Defs`, `Basic`, `Trace`, `Hard`, `Main`).
- `comparator.json`, `formalization.yaml` — Comparator configuration and registry metadata.

Build: `lake exe cache get && lake build`. Toolchain and Mathlib pin: `lean-toolchain`, `lakefile.toml`.

Submission form: https://submit.palomar-registry.org/
