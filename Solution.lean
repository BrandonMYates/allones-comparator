/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AllOnesLab

/-!
# Solution

The proof development lives in the `AllOnesLab` library in this repository. This file restates
the Challenge's three definitions and three theorems verbatim and discharges each theorem by the
corresponding library theorem. The three `example`s are the bridge: each Challenge definition is
definitionally equal to its `AllOnesLab` counterpart, checked by `rfl`.
-/

open Polynomial

namespace AllOnesGallardo

/-- The all-ones polynomial `1 + X + ⋯ + Xⁿ` over `𝔽₂ = ZMod 2`. -/
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i

/-- The substitution polynomial `P = X² + X + 1` over `𝔽₂`. -/
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1

/-- `1 + P + ⋯ + Pⁿ`, literally as in the OEIS comment. -/
noncomputable def allOnesP (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), P ^ i

example : @allOnes = @AllOnesLab.allOnes := rfl
example : P = AllOnesLab.P := rfl
example : @allOnesP = @AllOnesLab.allOnesP := rfl

/-- **P12771.** For `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂` iff `1 + P + ⋯ + Pⁿ` is. -/
theorem main (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) :=
  AllOnesLab.main n hn

/-- The set-level form of the OEIS A071642 comment: the terms `≥ 2` coincide. -/
theorem A071642_terms_ge_two :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} :=
  AllOnesLab.A071642_terms_ge_two

/-- The boundary case `n = 1` genuinely fails: `X + 1` is irreducible but `X² + X` is not. -/
theorem boundary_one : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) :=
  AllOnesLab.boundary_one

end AllOnesGallardo
