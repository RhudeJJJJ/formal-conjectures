/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalPolynomialCell

namespace Gebendorfer.RadenkovicGutman.RationalPolynomialOrder
open Polynomial PolynomialPathMap RationalComplexPolynomial RationalPolynomialCell
noncomputable section

theorem form_nonneg (p : ℚ[X]) (d : ℕ) (cs : Fin (d+1) → ℚ)
    (he : p = form d cs) (hc : ∀ i, 0 ≤ cs i) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ realEvaluator t p := by
  rw [he,form_evaluation]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (by exact_mod_cast hc i) (Bernstein.basis_nonneg d i t ht))

theorem form_positive (p : ℚ[X]) (d : ℕ) (cs : Fin (d+1) → ℚ)
    (he : p = form d cs) (hc : ∀ i, 0 < cs i) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < realEvaluator t p := by
  have hex : ∃ i : Fin (d+1), 0 < Bernstein.basis d i t := by
    by_contra! h
    have hh := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    rw [Bernstein.basis_sum] at hh
    norm_num at hh
  rw [he,form_evaluation]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ =>
    mul_nonneg (by exact_mod_cast (hc i).le) (Bernstein.basis_nonneg d i t ht))).mpr
  obtain ⟨i,hi⟩ := hex
  exact ⟨i,Finset.mem_univ _,mul_pos (by exact_mod_cast hc i) hi⟩

theorem list_nonneg (p : List ℚ) (hc : ∀ c ∈ p, 0 ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ realEvaluator t (ofList p) := by
  induction p with
  | nil => simp [ofList]
  | cons c p ih =>
      change 0 ≤ realEvaluator t (C c+X*ofList p)
      rw [map_add,map_mul,real_C,real_X]
      exact add_nonneg (by exact_mod_cast hc c (by simp))
        (mul_nonneg ht (ih (fun d hd => hc d (by simp [hd]))))

theorem list_positive (p : List ℚ) (hc : ∀ c ∈ p, 0 ≤ c)
    (h0 : 0 < p.headD 0) (t : ℝ) (ht : 0 ≤ t) :
    0 < realEvaluator t (ofList p) := by
  cases p with
  | nil => norm_num at h0
  | cons c p =>
      change 0 < realEvaluator t (C c+X*ofList p)
      rw [map_add,map_mul,real_C,real_X]
      have hp := list_nonneg p (fun d hd => hc d (by simp [hd])) t ht
      have hc0 : (0 : ℝ) < c := by exact_mod_cast h0
      exact add_pos_of_pos_of_nonneg hc0 (mul_nonneg ht hp)

def rayAccepts (p : ℚ[X]) (Y : ℚ) (cs : List ℚ) : Bool :=
  decide (p.comp (affine Y (Y+1)) = ofList cs ∧ ∀ c ∈ cs, 0 ≤ c)

theorem ray_nonneg (p : ℚ[X]) (Y : ℚ) (cs : List ℚ)
    (hc : rayAccepts p Y cs = true) (y : ℝ) (hy : (Y : ℝ) ≤ y) :
    0 ≤ realEvaluator y p := by
  obtain ⟨he,hn⟩ := of_decide_eq_true hc
  have hv := congrArg (realEvaluator (y-(Y : ℝ))) he
  rw [affine_evaluation] at hv
  have heq : (Y : ℝ)+(((Y+1 : ℚ) : ℝ)-Y)*(y-Y) = y := by push_cast; ring
  rw [heq] at hv
  rw [hv]
  exact list_nonneg cs hn _ (sub_nonneg.mpr hy)

theorem ray_positive (p : ℚ[X]) (Y : ℚ) (cs : List ℚ)
    (hc : rayAccepts p Y cs = true) (h0 : 0 < cs.headD 0)
    (y : ℝ) (hy : (Y : ℝ) ≤ y) : 0 < realEvaluator y p := by
  obtain ⟨he,hn⟩ := of_decide_eq_true hc
  have hv := congrArg (realEvaluator (y-(Y : ℝ))) he
  rw [affine_evaluation] at hv
  have heq : (Y : ℝ)+(((Y+1 : ℚ) : ℝ)-Y)*(y-Y) = y := by push_cast; ring
  rw [heq] at hv
  rw [hv]
  exact list_positive cs hn h0 _ (sub_nonneg.mpr hy)

#print axioms form_nonneg
#print axioms form_positive
#print axioms list_nonneg
#print axioms list_positive
#print axioms ray_nonneg
#print axioms ray_positive
end
end Gebendorfer.RadenkovicGutman.RationalPolynomialOrder
