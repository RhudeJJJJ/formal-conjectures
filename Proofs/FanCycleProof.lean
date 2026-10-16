import FormalConjectures.Arxiv.«2602.02046».CyclePolynomial

/-! Direct permutation enumeration and a complex-root certificate for the
five-vertex fan. The counting convention is exactly the imported one.
OpenAI Codex assisted with formalization and validation. -/
namespace FanCycleProof
open SimpleGraph Finset Polynomial YaqubiMirzavaziri.CyclePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def countCycles (σ : Equiv.Perm (Fin 5)) : ℕ :=
  σ.cycleFactorsFinset.card + (univ.filter fun v => σ v = v).card

def supported (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ v, σ v = v ∨ (v ≠ σ v ∧
    (v = 4 ∨ σ v = 4 ∨ Nat.dist v.val (σ v).val = 1))
instance : DecidablePred supported := fun σ =>
  inferInstanceAs (Decidable (∀ v, σ v = v ∨ (v ≠ σ v ∧
    (v = 4 ∨ σ v = 4 ∨ Nat.dist v.val (σ v).val = 1))))
def supportedPermutations : Finset (Equiv.Perm (Fin 5)) := univ.filter supported
def coefficientCount (k : ℕ) : ℕ :=
  (supportedPermutations.filter fun σ => countCycles σ = k).card
theorem enumeration : ∀ k : Fin 6,
    coefficientCount k = (![0,2,8,13,7,1] : Fin 6 → ℕ) k := by decide
theorem cycle_bound : ∀ σ : Equiv.Perm (Fin 5), countCycles σ ≤ 5 := by decide

theorem actual_polynomial :
    cyclePolynomial fanGraph = (X^5 + 7*X^4 + 13*X^3 + 8*X^2 + 2*X : ℝ[X]) := by
  classical
  have hcc : ∀ σ : Equiv.Perm (Fin 5), cycleCount σ = countCycles σ := by
    intro σ
    unfold cycleCount countCycles
    congr 1
  unfold cyclePolynomial
  change (∑ σ ∈ supportedPermutations, X ^ cycleCount σ) = _
  simp_rw [hcc]
  ext k
  have hcoeff : (∑ σ ∈ supportedPermutations, (X : ℝ[X]) ^ countCycles σ).coeff k =
      (coefficientCount k : ℝ) := by
    simp [Polynomial.coeff_sum, Polynomial.coeff_X_pow, coefficientCount,
      Finset.card_filter, Nat.cast_sum, eq_comm]
  rw [hcoeff]
  by_cases hk : k < 6
  · have hc := enumeration ⟨k,hk⟩
    interval_cases k <;> norm_num at hc ⊢ <;> exact_mod_cast hc
  · have hc : coefficientCount k = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro σ _
      have := cycle_bound σ
      omega
    rw [hc]
    norm_num
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, show k ≠ 0 by omega, show k ≠ 1 by omega,
      show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega,
      show k ≠ 5 by omega]

noncomputable def reciprocalQuartic : Polynomial ℂ := X^4 + 4*X^3 + C (13/2) * X^2 + C (7/2) * X + C (1/2)

theorem quartic_monic : reciprocalQuartic.Monic := by
  unfold reciprocalQuartic
  monicity <;> norm_num

theorem quartic_degree : reciprocalQuartic.natDegree = 4 := by
  unfold reciprocalQuartic
  compute_degree <;> norm_num

theorem quartic_no_real_roots_all :
    ¬ ∀ z : ℂ, reciprocalQuartic.eval z = 0 → z.im = 0 := by
  intro hreal
  have hsplit := IsAlgClosed.splits reciprocalQuartic
  have hcard : reciprocalQuartic.roots.card = 4 := by
    rw [hsplit.natDegree_eq_card_roots.symm, quartic_degree]
  obtain ⟨a,b,c,d,hroots⟩ := Multiset.card_eq_four.mp hcard
  have hfac := hsplit.eq_prod_roots_of_monic quartic_monic
  rw [hroots] at hfac
  change reciprocalQuartic = (X - C a) * ((X - C b) * ((X - C c) * (X - C d))) at hfac
  have hmem : ∀ z ∈ reciprocalQuartic.roots, z.im = 0 := by
    intro z hz
    exact hreal z ((Polynomial.mem_roots quartic_monic.ne_zero).mp hz)
  have ha : a.im = 0 := hmem a (by simp [hroots])
  have hb : b.im = 0 := hmem b (by simp [hroots])
  have hc : c.im = 0 := hmem c (by simp [hroots])
  have hd : d.im = 0 := hmem d (by simp [hroots])
  have hs := congrArg (fun p : ℂ[X] => (p.coeff 3).re) hfac
  have hp := congrArg (fun p : ℂ[X] => (p.coeff 2).re) hfac
  norm_num [reciprocalQuartic, Polynomial.coeff_mul, Finset.sum_range_succ,
    ha, hb, hc, hd, Complex.mul_re] at hs hp
  apply fan_reciprocal_coefficient_obstruction a.re b.re c.re d.re
  · linarith
  · linarith

theorem fan_not_realRooted : ¬ IsRealRooted (cyclePolynomial fanGraph) := by
  intro h
  apply quartic_no_real_roots_all
  intro z hz
  have he : z^4 + 4*z^3 + (13/2)*z^2 + (7/2)*z + 1/2 = 0 := by
    simpa [reciprocalQuartic] using hz
  have hn : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at he
  have hpoly : (cyclePolynomial fanGraph).eval₂ (algebraMap ℝ ℂ) z⁻¹ = 0 := by
    rw [actual_polynomial]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
    field_simp
    linear_combination 2 * he
  have hi := h z⁻¹ hpoly
  have hzinv : (z⁻¹ : ℂ) = ((z⁻¹).re : ℂ) := by
    apply Complex.ext <;> simp [hi]
  have hzreal : z = (((z⁻¹).re)⁻¹ : ℝ) := by
    calc
      z = (z⁻¹)⁻¹ := (inv_inv z).symm
      _ = (((z⁻¹).re : ℂ))⁻¹ := congrArg Inv.inv hzinv
      _ = _ := by simp
  rw [hzreal]
  simp

theorem conjecture6_2 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.IsChordal → IsRealRooted (cyclePolynomial G) := by
  intro h
  exact fan_not_realRooted (h 5 fanGraph fan_isChordal)

end FanCycleProof
#print axioms FanCycleProof.conjecture6_2
#print axioms FanCycleProof.enumeration
#print axioms FanCycleProof.quartic_no_real_roots_all
