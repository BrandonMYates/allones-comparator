import AllOnesLab.Basic

/-!
# Trace lemmas for `allOnes`

Three trace facts used by the irreducibility argument:

* `trace_sq_add_self_eq_zero` — over `𝔽₂`, elements of the form `z² + z` have trace `0`
  (Frobenius-invariance of the trace);
* `trace_root_allOnes` — the root of `allOnes n` in `AdjoinRoot (allOnes n)` has trace `1`;
* `trace_one_allOnes` — `Tr(1) = n` because `finrank = n`.
-/

open Polynomial

namespace AllOnesLab


/-! ### Small arithmetic facts in `ZMod 2` -/

private lemma zmod_two_add_self : ∀ t : ZMod 2, t + t = 0 := by decide

private lemma zmod_two_neg_one : -(1 : ZMod 2) = 1 := by decide

/-! ### Frobenius invariance of the trace -/

/-- In a finite-dimensional field extension of 𝔽₂, `z² + z` has trace zero
    (trace is Frobenius-invariant: Tr(z²) = Tr(z)). -/
theorem trace_sq_add_self_eq_zero {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (z : K) :
    Algebra.trace (ZMod 2) K (z ^ 2 + z) = 0 := by
  haveI halg : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
  -- the Frobenius `x ↦ x ^ 2` is a `ZMod 2`-algebra automorphism of `K`
  let e : K ≃ₐ[ZMod 2] K := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hcard : Fintype.card (ZMod 2) = 2 := by simp
  have hez : e z = z ^ 2 := by
    have h1 : e z = z ^ Fintype.card (ZMod 2) :=
      congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic (ZMod 2) K) z
    rw [h1, hcard]
  have hsq : Algebra.trace (ZMod 2) K (z ^ 2) = Algebra.trace (ZMod 2) K z := by
    rw [← hez]
    exact Algebra.trace_eq_of_algEquiv e z
  rw [map_add, hsq, zmod_two_add_self]

/-! ### Trace of the root -/

/-- The minimal polynomial of the root of a monic `f` over a field is `f` itself. -/
private lemma minpoly_root_of_monic {F : Type*} [Field F] {f : F[X]} (hf : f.Monic) :
    minpoly F (AdjoinRoot.root f) = f := by
  rw [AdjoinRoot.minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one]

/-- The root of `allOnes n` in `AdjoinRoot (allOnes n)` has trace 1 (from the Xⁿ⁻¹ coefficient). -/
theorem trace_root_allOnes (n : ℕ) (hn : 1 ≤ n) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) (AdjoinRoot.root (allOnes n)) = 1 := by
  have hm : (allOnes n).Monic := allOnes_monic n
  haveI hnt : Nontrivial (AdjoinRoot (allOnes n)) := by
    refine AdjoinRoot.nontrivial _ ?_
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, allOnes_natDegree]
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpb := (AdjoinRoot.powerBasis' hm).trace_gen_eq_nextCoeff_minpoly
  rw [AdjoinRoot.powerBasis'_gen, minpoly_root_of_monic hm, allOnes_nextCoeff n hn,
    zmod_two_neg_one] at hpb
  exact hpb

/-! ### Trace of one -/

/-- Trace of 1 in `AdjoinRoot (allOnes n)` is `n` (finrank = n). -/
theorem trace_one_allOnes (n : ℕ) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) 1 = (n : ZMod 2) := by
  have hm : (allOnes n).Monic := allOnes_monic n
  have hrank : Module.finrank (ZMod 2) (AdjoinRoot (allOnes n)) = n := by
    rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, allOnes_natDegree]
  have h := Algebra.trace_algebraMap (R := ZMod 2) (S := AdjoinRoot (allOnes n)) 1
  rw [map_one, hrank] at h
  rw [h, nsmul_eq_mul, mul_one]

#print axioms trace_sq_add_self_eq_zero
#print axioms trace_root_allOnes
#print axioms trace_one_allOnes

end AllOnesLab
