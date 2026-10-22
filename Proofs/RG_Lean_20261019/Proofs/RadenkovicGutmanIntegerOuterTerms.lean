/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerAffineStages

namespace Gebendorfer.RadenkovicGutman.IntegerOuterTerms
open NestedInteger NestedHorner Finset
set_option maxHeartbeats 0

/-- The finite binomial expansion of a single shifted monomial. -/
def term {n : ℕ} (k : ℕ) (l w K : ℤ) (c : NestedInteger.Poly n) :
    NestedInteger.Poly (n+1) :=
  List.ofFn (fun j : Fin (k+1) => NestedInteger.scale
    (K*(Nat.fast_choose k j.val : ℤ)*l^(k-j.val)*w^j.val) c)

/-- Each coefficient contributes once. In particular, the recursively prepared
tail is not duplicated by the two arms of a Horner substitution. -/
def transform {n : ℕ} (l w D : ℤ) : ℕ → NestedInteger.Poly (n+1) → NestedInteger.Poly (n+1)
  | _,[] => []
  | k,c::p => NestedInteger.add (term k l w (D^p.length) c) (transform l w D (k+1) p)

noncomputable section
theorem eval_ofFn {n : ℕ} (N : ℕ) (f : Fin N → NestedInteger.Poly n)
    (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) (List.ofFn f)) x=
      ∑ j : Fin N, eval (castPoly n (f j)) (fun i => x i.succ)*x 0^j.val := by
  induction N with
  | zero => simp [List.ofFn_zero,castPoly,eval]
  | succ N ih =>
    rw [List.ofFn_succ]
    change eval (castPoly n (f 0)::castPoly (n+1) (List.ofFn (fun j => f j.succ))) x=_
    rw [eval_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,pow_zero,mul_one]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

theorem eval_term {n : ℕ} (k : ℕ) (l w K : ℤ) (c : NestedInteger.Poly n)
    (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) (term k l w K c)) x=
      (K : ℝ)*((l : ℝ)+(w : ℝ)*x 0)^k*eval (castPoly n c) (fun i => x i.succ) := by
  rw [term,eval_ofFn,add_comm (l : ℝ),add_pow]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j : ℕ => ((w : ℝ)*x 0)^j*(l : ℝ)^(k-j)*(k.choose j : ℝ)) (k+1)]
  simp only [cast_scale,eval_scale,← Nat.choose_eq_fast_choose]
  push_cast
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

theorem eval_from {n : ℕ} (l w D : ℤ) (hD : D ≠ 0) (k : ℕ)
    (p : NestedInteger.Poly (n+1)) (x : Fin (n+1) → ℝ) :
    (D : ℝ)*eval (castPoly (n+1) (transform l w D k p)) x=
      ((l : ℝ)+(w : ℝ)*x 0)^k*(D : ℝ)^p.length*
        eval (castPoly (n+1) p)
          (Fin.cons (((l : ℝ)+(w : ℝ)*x 0)/(D : ℝ)) (fun i => x i.succ)) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  induction p generalizing k with
  | nil => simp [transform,castPoly,eval]
  | cons c p ih =>
    rw [transform,cast_add,eval_add,eval_term,mul_add,ih]
    change _=_*(_ : ℝ)^(p.length+1)*
      (eval (castPoly n c) (fun i => x i.succ)+
        (((l : ℝ)+(w : ℝ)*x 0)/(D : ℝ))*
          eval (castPoly (n+1) p) (Fin.cons _ _))
    push_cast
    rw [pow_succ,pow_succ]
    field_simp

/-- The new finite coefficient transform has exactly the old substitution's
semantics. Its data is still checked by the Lean kernel at every concrete use. -/
theorem eval_eq_clearedOuter {n : ℕ} (l w D : ℤ) (hD : D ≠ 0)
    (p : NestedInteger.Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (castPoly (n+1) (transform l w D 0 p)) x=
      eval (castPoly (n+1) (NestedInteger.clearedOuter l w D p)) x := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  apply (mul_left_cancel₀ hDr)
  rw [eval_from l w D hD,NestedInteger.clearedOuter_sound l w D p x hD]
  simp only [pow_zero,one_mul]

#print axioms eval_ofFn
#print axioms eval_term
#print axioms eval_from
#print axioms eval_eq_clearedOuter
end
end Gebendorfer.RadenkovicGutman.IntegerOuterTerms
