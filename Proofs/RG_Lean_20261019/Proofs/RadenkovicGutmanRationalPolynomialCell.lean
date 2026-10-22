/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalComplexPolynomial
import Proofs.RadenkovicGutmanBernstein

namespace Gebendorfer.RadenkovicGutman.RationalPolynomialCell
noncomputable section
open Polynomial PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0

def affine (a b : ℚ) : ℚ[X] := C a+C (b-a)*X
def form (d : ℕ) (cs : Fin (d+1) → ℚ) : ℚ[X] :=
  ∑ i, C (cs i)*bernsteinPolynomial ℚ d i
def accepts (p : List ℚ) (a b : ℚ) (d : ℕ) (cs : Fin (d+1) → ℚ) : Bool :=
  decide ((ofList p).comp (affine a b)=form d cs)

theorem affine_evaluation (p : ℚ[X]) (a b : ℚ) (t : ℝ) :
    realEvaluator t (p.comp (affine a b))=
      realEvaluator ((a : ℝ)+((b : ℝ)-(a : ℝ))*t) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.add_comp,map_add,hp,hq]
  | monomial n c =>
    simp only [Polynomial.monomial_comp,map_mul,map_pow,real_C]
    simp only [affine,map_add,map_mul,real_C,real_X]
    simp [realEvaluator]

theorem basis_evaluation (d : ℕ) (i : Fin (d+1)) (t : ℝ) :
    realEvaluator t (bernsteinPolynomial ℚ d i)=Bernstein.basis d i t := by
  unfold Bernstein.basis bernsteinPolynomial
  simp only [map_mul,map_pow,map_natCast,map_sub,map_one,real_X,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_natCast,
    Polynomial.eval_X,Polynomial.eval_sub,Polynomial.eval_one]

theorem form_evaluation (d : ℕ) (cs : Fin (d+1) → ℚ) (t : ℝ) :
    realEvaluator t (form d cs)=∑ i, (cs i : ℝ)*Bernstein.basis d i t := by
  unfold form
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,real_C,basis_evaluation]

/-- Kernel-checked polynomial equality proves the representation on the entire
real cell, including irrational ordinates. -/
theorem representation (p : List ℚ) (a b : ℚ) (d : ℕ) (cs : Fin (d+1) → ℚ)
    (hc : accepts p a b d cs=true) (y : ℝ) (hab : a < b) :
    realEvaluator y (ofList p)=
      ∑ i, (cs i : ℝ)*Bernstein.basis d i ((y-a)/(b-a)) := by
  have he : (ofList p).comp (affine a b)=form d cs := of_decide_eq_true hc
  have habr : (a : ℝ) < b := by exact_mod_cast hab
  have hr : (a : ℝ)+((b : ℝ)-a)*((y-a)/(b-a))=y := by
    field_simp [ne_of_gt (sub_pos.mpr habr)]
    all_goals ring
  have hh := congrArg (realEvaluator ((y-a)/(b-a))) he
  rw [affine_evaluation,form_evaluation,hr] at hh
  exact hh

theorem cell_coordinate (a b : ℚ) (hab : a < b) (y : ℝ)
    (hy : y ∈ Set.Icc (a : ℝ) (b : ℝ)) : (y-a)/(b-a) ∈ Set.Icc (0 : ℝ) 1 := by
  have habr : (a : ℝ) < b := by exact_mod_cast hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hy.1) (sub_pos.mpr habr).le
  · apply (div_le_one (sub_pos.mpr habr)).mpr
    linarith only [hy.2]

theorem nonneg (p : List ℚ) (a b : ℚ) (d : ℕ) (cs : Fin (d+1) → ℚ)
    (hc : accepts p a b d cs=true) (hcs : ∀ i, 0 ≤ cs i) (hab : a < b)
    (y : ℝ) (hy : y ∈ Set.Icc (a : ℝ) (b : ℝ)) : 0 ≤ realEvaluator y (ofList p) := by
  rw [representation p a b d cs hc y hab]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (by exact_mod_cast hcs i)
    (Bernstein.basis_nonneg d i _ (cell_coordinate a b hab y hy))

theorem positive (p : List ℚ) (a b : ℚ) (d : ℕ) (cs : Fin (d+1) → ℚ)
    (hc : accepts p a b d cs=true) (hcs : ∀ i, 0 < cs i) (hab : a < b)
    (y : ℝ) (hy : y ∈ Set.Icc (a : ℝ) (b : ℝ)) : 0 < realEvaluator y (ofList p) := by
  let t := (y-a)/(b-a)
  have ht := cell_coordinate a b hab y hy
  have hex : ∃ i : Fin (d+1), 0 < Bernstein.basis d i t := by
    by_contra! h
    have hh := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
    rw [Bernstein.basis_sum] at hh
    norm_num at hh
  rw [representation p a b d cs hc y hab]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ =>
    mul_nonneg (by exact_mod_cast (hcs i).le) (Bernstein.basis_nonneg d i _ ht))).mpr
  obtain ⟨i,hi⟩ := hex
  exact ⟨i,Finset.mem_univ _,mul_pos (by exact_mod_cast hcs i) hi⟩

theorem linear_control : accepts [1,1] 1 2 1 ![2,3]=true := by
  rw [accepts,decide_eq_true_eq]
  apply Polynomial.funext
  intro t
  norm_num [ofList,affine,form,bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  all_goals ring
theorem rejects_false_control : accepts [1,1] 1 2 1 ![2,4]=false := by
  rw [accepts,decide_eq_false_iff_not]
  intro h
  have he := congrArg (fun p : ℚ[X] => p.eval 1) h
  norm_num [ofList,affine,form,bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ] at he

#print axioms affine_evaluation
#print axioms basis_evaluation
#print axioms form_evaluation
#print axioms representation
#print axioms cell_coordinate
#print axioms nonneg
#print axioms positive
#print axioms linear_control
#print axioms rejects_false_control
end
end Gebendorfer.RadenkovicGutman.RationalPolynomialCell
