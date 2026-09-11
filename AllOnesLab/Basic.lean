import AllOnesLab.Defs

/-!
# Basic structure theory of the all-ones polynomials over `𝔽₂`

Coefficients, degree and monicity of `allOnes n = 1 + X + ⋯ + Xⁿ`, the identification
`allOnesP n = (allOnes n).comp P`, and the two easy halves of P12771:

* `even_of_irreducible_allOnes` — odd `n ≥ 2` is reducible (the root `X = 1`);
* `irreducible_allOnes_of_irreducible_allOnesP` — a factorisation of `allOnes n`
  composes with `P` to a factorisation of `allOnesP n`.
-/

open Polynomial

namespace AllOnesLab

/-! ### Characteristic-two bookkeeping -/

/-- `2 = 0` in `𝔽₂[X]`. -/
private lemma two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  simpa using CharP.cast_eq_zero ((ZMod 2)[X]) 2

/-! ### The substitution polynomial `P = X² + X + 1` -/

theorem P_monic : P.Monic := by
  unfold P
  monicity!

theorem P_natDegree : P.natDegree = 2 := by
  unfold P
  compute_degree!

private lemma P_natDegree_ne_zero : P.natDegree ≠ 0 := by
  rw [P_natDegree]; omega

/-! ### Coefficients of `allOnes` -/

/-- All coefficients up to `n` are `1`, the rest vanish. -/
theorem allOnes_coeff_eq (n i : ℕ) : (allOnes n).coeff i = if i ≤ n then 1 else 0 := by
  rw [allOnes, finsetSum_coeff]
  simp

theorem allOnes_coeff (n i : ℕ) (hi : i ≤ n) : (allOnes n).coeff i = 1 := by
  rw [allOnes_coeff_eq, if_pos hi]

theorem allOnes_coeff_of_lt (n i : ℕ) (hi : n < i) : (allOnes n).coeff i = 0 := by
  rw [allOnes_coeff_eq, if_neg (by omega : ¬ i ≤ n)]

/-! ### Degree and monicity of `allOnes` -/

theorem allOnes_natDegree (n : ℕ) : (allOnes n).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN => allOnes_coeff_of_lt n N hN
  · rw [allOnes_coeff n n le_rfl]
    exact one_ne_zero

theorem allOnes_monic (n : ℕ) : (allOnes n).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (allOnes_natDegree n).le (allOnes_coeff n n le_rfl)

theorem allOnes_nextCoeff (n : ℕ) (hn : 1 ≤ n) : (allOnes n).nextCoeff = 1 := by
  rw [nextCoeff_of_natDegree_pos (by rw [allOnes_natDegree]; omega), allOnes_natDegree]
  exact allOnes_coeff n (n - 1) (by omega)

/-! ### Evaluation at `1` -/

theorem allOnes_eval_one (n : ℕ) : (allOnes n).eval 1 = (n + 1 : ZMod 2) := by
  have h : (allOnes n).eval 1 = ∑ _i ∈ Finset.range (n + 1), (1 : ZMod 2) := by
    rw [allOnes, eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]

/-! ### `allOnesP` as a composition -/

theorem allOnesP_eq_comp (n : ℕ) : allOnesP n = (allOnes n).comp P := by
  rw [allOnes, allOnesP, Polynomial.sum_comp]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_comp, X_comp]

theorem allOnesP_monic (n : ℕ) : (allOnesP n).Monic := by
  rw [allOnesP_eq_comp]
  exact (allOnes_monic n).comp P_monic P_natDegree_ne_zero

theorem allOnesP_natDegree (n : ℕ) : (allOnesP n).natDegree = 2 * n := by
  rw [allOnesP_eq_comp, natDegree_comp, allOnes_natDegree, P_natDegree, Nat.mul_comm]

/-! ### Odd `n ≥ 2` is reducible -/

/-- Odd n ≥ 2 forces reducibility: X + 1 divides since eval 1 = n + 1 = 0. -/
theorem even_of_irreducible_allOnes (n : ℕ) (hn : 2 ≤ n) (h : Irreducible (allOnes n)) :
    Even n := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ : 2 ∣ n + 1 := by
    have := Nat.odd_iff.mp hodd
    omega
  have hcast : ((n + 1 : ℕ) : ZMod 2) = 0 := by
    rw [hk]
    push_cast
    simp [show (2 : ZMod 2) = 0 by decide]
  have hroot : (allOnes n).IsRoot 1 := by
    rw [Polynomial.IsRoot.def, allOnes_eval_one]
    push_cast at hcast
    exact hcast
  exact h.not_isRoot_of_natDegree_ne_one (by rw [allOnes_natDegree]; omega) hroot

/-! ### The easy direction -/

private lemma natDegree_comp_P (a : (ZMod 2)[X]) : (a.comp P).natDegree = 2 * a.natDegree := by
  rw [natDegree_comp, P_natDegree, Nat.mul_comm]

/-- Substituting `P` cannot turn a non-unit into a unit: `natDegree (a.comp P) = 2 natDegree a`. -/
private lemma isUnit_of_isUnit_comp_P {a : (ZMod 2)[X]} (h : IsUnit (a.comp P)) : IsUnit a := by
  have hdeg : a.natDegree = 0 := by
    have h0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_comp_P] at h0
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_comp] at h
    simp at h
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hdeg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact ha hc.symm
  rw [← hc, isUnit_C]
  exact isUnit_iff_ne_zero.mpr hc0

/-- The easy direction of P12771: a factorization of allOnes n composes to one of allOnesP n. -/
theorem irreducible_allOnes_of_irreducible_allOnesP (n : ℕ) (hn : 2 ≤ n)
    (h : Irreducible (allOnesP n)) : Irreducible (allOnes n) := by
  constructor
  · exact not_isUnit_of_natDegree_pos _ (by rw [allOnes_natDegree]; omega)
  · intro a b hab
    have hcomp : allOnesP n = a.comp P * b.comp P := by
      rw [allOnesP_eq_comp, hab, mul_comp]
    rcases h.isUnit_or_isUnit hcomp with hu | hu
    · exact Or.inl (isUnit_of_isUnit_comp_P hu)
    · exact Or.inr (isUnit_of_isUnit_comp_P hu)

/-! ### The boundary case `n = 1` -/

/-- Boundary: n = 1 fails. X + 1 is irreducible; X² + X = X (X + 1) is not. -/
theorem boundary_one' : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) := by
  refine ⟨?_, ?_⟩
  · have h1 : allOnes 1 = X + C (1 : ZMod 2) := by
      rw [allOnes, Finset.sum_range_succ, Finset.sum_range_one, Polynomial.C_1, pow_zero, pow_one,
        add_comm]
    rw [h1]
    exact (monic_X_add_C (1 : ZMod 2)).irreducible_of_degree_eq_one (degree_X_add_C 1)
  · intro h
    have h1 : allOnesP 1 = 1 + P := by
      simp [allOnesP, Finset.sum_range_succ]
    have hfac : allOnesP 1 = X * (X + 1) := by
      rw [h1]
      simp only [P]
      linear_combination two_eq_zero_poly
    have hX : (X : (ZMod 2)[X]).natDegree = 1 := natDegree_X
    have hX1 : (X + 1 : (ZMod 2)[X]).natDegree = 1 := by compute_degree!
    rcases h.isUnit_or_isUnit hfac with hu | hu
    · exact not_isUnit_of_natDegree_pos _ (by omega) hu
    · exact not_isUnit_of_natDegree_pos _ (by omega) hu

end AllOnesLab

#print axioms AllOnesLab.P_monic
#print axioms AllOnesLab.P_natDegree
#print axioms AllOnesLab.allOnes_coeff
#print axioms AllOnesLab.allOnes_coeff_of_lt
#print axioms AllOnesLab.allOnes_monic
#print axioms AllOnesLab.allOnes_natDegree
#print axioms AllOnesLab.allOnes_nextCoeff
#print axioms AllOnesLab.allOnes_eval_one
#print axioms AllOnesLab.allOnesP_eq_comp
#print axioms AllOnesLab.allOnesP_monic
#print axioms AllOnesLab.allOnesP_natDegree
#print axioms AllOnesLab.even_of_irreducible_allOnes
#print axioms AllOnesLab.irreducible_allOnes_of_irreducible_allOnesP
#print axioms AllOnesLab.boundary_one'
