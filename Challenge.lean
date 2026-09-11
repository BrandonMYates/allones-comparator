/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: all-ones polynomials over 𝔽₂ under the substitution `X ↦ X² + X + 1`

This is the human-auditable statement surface. It imports only Mathlib.

## The statement

OEIS A071642 lists the `n` for which the all-ones polynomial `1 + X + ⋯ + Xⁿ` is irreducible
over `GF(2)`. Its comment (L. H. Gallardo, 23 Dec 2019) conjectures that the terms `≥ 2` are
exactly the `n` for which `1 + P + ⋯ + Pⁿ` is irreducible over `GF(2)`, where `P = X² + X + 1`.
TheoremDB records the question as P12771.

`main` states the equivalence for each `n ≥ 2`; `A071642_terms_ge_two` is the literal set-level
form of the OEIS comment; `boundary_one` records that the excluded case `n = 1` genuinely fails.

## Definitions

`𝔽₂` is Mathlib's `ZMod 2`; polynomials are `Polynomial (ZMod 2)`. The three definitions below
are the obvious transcriptions and are used with no other meaning.
-/

open Polynomial

namespace AllOnesGallardo

/-- The all-ones polynomial `1 + X + ⋯ + Xⁿ` over `𝔽₂ = ZMod 2`. -/
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i

/-- The substitution polynomial `P = X² + X + 1` over `𝔽₂`. -/
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1

/-- `1 + P + ⋯ + Pⁿ`, literally as in the OEIS comment. -/
noncomputable def allOnesP (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), P ^ i

/-- **P12771.** For `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂` iff `1 + P + ⋯ + Pⁿ` is. -/
theorem main (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) := by
  sorry

/-- The set-level form of the OEIS A071642 comment: the terms `≥ 2` coincide. -/
theorem A071642_terms_ge_two :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} := by
  sorry

/-- The boundary case `n = 1` genuinely fails: `X + 1` is irreducible but `X² + X` is not. -/
theorem boundary_one : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by
  sorry

end AllOnesGallardo
