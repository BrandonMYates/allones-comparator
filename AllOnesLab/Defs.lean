import Mathlib

/-!
# All-ones polynomials over 𝔽₂ under the substitution X ↦ X² + X + 1

Formal statement surface for OEIS A071642 / TheoremDB P12771 (conjecture of
L. H. Gallardo, 2019): for `n ≥ 2`, `1 + X + ⋯ + Xⁿ` is irreducible over `𝔽₂`
iff `1 + P + ⋯ + Pⁿ` is irreducible over `𝔽₂`, where `P = X² + X + 1`.
-/

open Polynomial

namespace AllOnesLab

/-- The all-ones polynomial `1 + X + ⋯ + Xⁿ` over `𝔽₂ = ZMod 2`. -/
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i

/-- The substitution polynomial `P = X² + X + 1` over `𝔽₂`. -/
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1

/-- `1 + P + ⋯ + Pⁿ`, literally as in the OEIS comment. -/
noncomputable def allOnesP (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), P ^ i

end AllOnesLab
