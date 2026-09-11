import AllOnesLab.Hard

/-!
# Main results for OEIS A071642 / TheoremDB P12771
-/

open Polynomial

namespace AllOnesLab

/-- **P12771.** For `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂` iff `1 + P + ⋯ + Pⁿ` is. -/
theorem main (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (allOnes n) ↔ Irreducible (allOnesP n) :=
  ⟨irreducible_allOnesP_of_irreducible_allOnes n hn,
   irreducible_allOnes_of_irreducible_allOnesP n hn⟩

/-- The set-level form of the OEIS A071642 comment: the terms `≥ 2` coincide. -/
theorem A071642_terms_ge_two :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} := by
  ext n
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨h, hi⟩ => ⟨h, (main n h).1 hi⟩, fun ⟨h, hi⟩ => ⟨h, (main n h).2 hi⟩⟩

/-- The boundary case `n = 1` genuinely fails: `X + 1` is irreducible but `X² + X` is not. -/
theorem boundary_one : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) :=
  boundary_one'

#print axioms main
#print axioms A071642_terms_ge_two
#print axioms boundary_one

end AllOnesLab
