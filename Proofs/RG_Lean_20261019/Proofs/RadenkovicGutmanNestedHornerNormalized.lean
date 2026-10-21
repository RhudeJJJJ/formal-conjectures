/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedHornerTransform
namespace Gebendorfer.RadenkovicGutman.NestedHornerNormalized
open NestedHorner
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false

def trimTrailingZeros {A : Type*} [DecidableEq A] (z : A) : List A → List A
  | [] => []
  | c :: p =>
    let q := trimTrailingZeros z p
    if q=[] ∧ c=z then [] else c::q

def normalize : (n : ℕ) → Poly n → Poly n
  | 0, p => p
  | n+1, p => @trimTrailingZeros (Poly n) (polyDecidableEq n) (zero n) (p.map (normalize n))

theorem eval_trimTrailingZeros (n : ℕ) (p : Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (@trimTrailingZeros (Poly n) (polyDecidableEq n) (zero n) p) x=eval p x := by
  let _ : DecidableEq (Poly n) := polyDecidableEq n
  induction p with
  | nil => rfl
  | cons c p ih =>
    change eval (if trimTrailingZeros (zero n) p=[] ∧ c=zero n then []
      else c::trimTrailingZeros (zero n) p) x=eval (c::p) x
    split_ifs with h
    · have hp : eval p x=0 := by rw [← ih,h.1]; rfl
      change (0 : ℝ)=eval c (fun i => x i.succ)+x 0*eval p x
      rw [h.2,eval_zero,hp,mul_zero,zero_add]
    · change eval c (fun i => x i.succ)+x 0*eval (trimTrailingZeros (zero n) p) x=
        eval c (fun i => x i.succ)+x 0*eval p x
      rw [ih]

theorem eval_normalize (n : ℕ) (p : Poly n) (x : Fin n → ℝ) :
    eval (normalize n p) x=eval p x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [normalize,eval_trimTrailingZeros]
    induction p with
    | nil => rfl
    | cons c p hp =>
      change eval (normalize n c) (fun i => x i.succ)+x 0*eval (p.map (normalize n)) x=
        eval c (fun i => x i.succ)+x 0*eval p x
      rw [ih,hp]

def affineCheck (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ) : Bool :=
  letI : DecidableEq (Poly n) := polyDecidableEq n
  decide (normalize n a=normalize n (affineAll n p l w))

theorem affineCheck_sound (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ)
    (hc : affineCheck n p a l w=true) (x : Fin n → ℝ) :
    eval a x=eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
  let _ : DecidableEq (Poly n) := polyDecidableEq n
  change decide (normalize n a=normalize n (affineAll n p l w))=true at hc
  have he : normalize n a=normalize n (affineAll n p l w) := of_decide_eq_true hc
  calc
    eval a x=eval (normalize n a) x := (eval_normalize n a x).symm
    _ = eval (normalize n (affineAll n p l w)) x := congrArg (fun q => eval q x) he
    _ = eval (affineAll n p l w) x := eval_normalize n _ x
    _ = eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := affineAll_sound n p l w x

theorem padding_rejects_raw_list_identity :
    affineCheckFast 2 [[1],[0,1]] [[1],[0,1]] ![0,0] ![1,1]=false := by decide +kernel
theorem normalized_padding_identity :
    affineCheck 2 [[1],[0,1]] [[1],[0,1]] ![0,0] ![1,1]=true := by decide +kernel
theorem changed_constant_rejected :
    affineCheck 2 [[1],[0,1]] [[2],[0,1]] ![0,0] ![1,1]=false := by decide +kernel
theorem fractional_affine_control :
    affineCheck 1 [0,1] [1/3,2/3] ![1/3] ![2/3]=true := by decide +kernel
theorem fractional_four_coordinate_control :
    affineCheck 4 [[[[0]]],[[[3]]]] [[[[1]]],[[[2]]]]
      ![1/3,0,0,0] ![2/3,1,1,1]=true := by decide +kernel

#print axioms eval_trimTrailingZeros
#print axioms eval_normalize
#print axioms affineCheck_sound
#print axioms padding_rejects_raw_list_identity
#print axioms normalized_padding_identity
#print axioms changed_constant_rejected
#print axioms fractional_affine_control
#print axioms fractional_four_coordinate_control
end Gebendorfer.RadenkovicGutman.NestedHornerNormalized
