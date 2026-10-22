/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedArithmetic

namespace Gebendorfer.RadenkovicGutman.NestedAffine
open NestedHorner NestedArithmetic
set_option maxHeartbeats 0

/-- Exact coefficient substitution, using Horner multiplication by a linear polynomial. -/
def transform : (n : ℕ) → Poly n → (Fin n → ℚ) → (Fin n → ℚ) → Poly n
  | 0,p,_,_ => p
  | n+1,p,l,w => p.foldr (fun c a =>
      add [transform n c (fun i => l i.succ) (fun i => w i.succ)]
        (mul [constant n (l 0),constant n (w 0)] a)) []

def zeroCheck : (n : ℕ) → Poly n → Bool
  | 0,p => decide (p=0)
  | n+1,p => p.all (zeroCheck n)

def check (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ) : Bool :=
  zeroCheck n (add (transform n p l w) (scale (-1) a))

noncomputable section
theorem transform_sound (n : ℕ) (p : Poly n) (l w : Fin n → ℚ) (x : Fin n → ℝ) :
    eval (transform n p l w) x = eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction p with
    | nil => simp [transform]
    | cons c p hp =>
      simp only [transform] at hp
      simp only [transform,List.foldr_cons,eval_add,eval_mul,eval_cons,eval_nil,
        mul_zero,add_zero,eval_constant]
      rw [ih,hp]
      ring

theorem zeroCheck_sound (n : ℕ) (p : Poly n) (h : zeroCheck n p=true) (x : Fin n → ℝ) :
    eval p x=0 := by
  induction n with
  | zero =>
    have hp : p=0 := of_decide_eq_true h
    subst p
    norm_num [eval]
  | succ n ih =>
    induction p with
    | nil => rfl
    | cons c p hp =>
      have hh : zeroCheck n c=true ∧ zeroCheck (n+1) p=true := by
        simpa only [zeroCheck,List.all_cons,Bool.and_eq_true] using h
      simp only [eval_cons,ih c hh.1 (fun i => x i.succ),hp hh.2,mul_zero,add_zero]

theorem check_sound (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ)
    (h : check n p a l w=true) (x : Fin n → ℝ) :
    eval a x=eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
  have hh := zeroCheck_sound n _ h x
  rw [eval_add,eval_scale,transform_sound] at hh
  norm_num only [Rat.cast_neg,Rat.cast_one] at hh
  linarith only [hh]

#print axioms transform_sound
#print axioms zeroCheck_sound
#print axioms check_sound
end
end Gebendorfer.RadenkovicGutman.NestedAffine
