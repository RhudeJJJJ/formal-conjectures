/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact affine substitution by polynomial arithmetic. The supplied transformed
coefficients are compared with a proved recursive transformation in the kernel.
-/
import Proofs.RadenkovicGutmanNestedHornerCells
namespace Gebendorfer.RadenkovicGutman.NestedHorner
open Set
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def polyDecidableEq (n : ℕ) : DecidableEq (Poly n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq ℚ)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (List (Poly n)))

def affineOuter {n : ℕ} (l w : ℚ) : Poly (n+1) → Poly (n+1)
  | [] => []
  | c :: p =>
    let q := affineOuter l w p
    add [c] (add (scale l q) (zero n :: scale w q))

def affineAll : (n : ℕ) → Poly n → (Fin n → ℚ) → (Fin n → ℚ) → Poly n
  | 0, p, _, _ => p
  | n+1, p, l, w => affineOuter (l 0) (w 0)
      (p.map (fun c => affineAll n c (fun i => l i.succ) (fun i => w i.succ)))

def affineCheckFast (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ) : Bool :=
  @decide (a = affineAll n p l w) (polyDecidableEq n a (affineAll n p l w))

def powerCheck : (n : ℕ) → Poly n → Bool
  | 0, p => decide (0 ≤ p)
  | n+1, p => p.all (powerCheck n)

def positiveCheckCombined (n : ℕ) (d : Fin n → ℕ) (p : Poly n) : Bool :=
  powerCheck n p || positiveCheck n d p

theorem powerCheck_sound (n : ℕ) (p : Poly n) (hc : powerCheck n p = true)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval p x := by
  induction n with
  | zero =>
    change (0 : ℝ) ≤ (p : ℝ)
    exact_mod_cast (of_decide_eq_true hc : (0 : ℚ) ≤ p)
  | succ n ih =>
    induction p with
    | nil => exact le_rfl
    | cons c p hp =>
      have hh : powerCheck n c = true ∧ p.all (powerCheck n) = true := by
        simpa only [powerCheck, List.all_cons, Bool.and_eq_true] using hc
      change 0 ≤ eval c (fun i => x i.succ)+x 0*eval p x
      exact add_nonneg (ih c hh.1 _ (fun i => hx i.succ)) (mul_nonneg (hx 0) (hp hh.2))

theorem positiveCheckCombined_sound (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hc : positiveCheckCombined n d p = true) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) : 0 ≤ eval p x := by
  have hh : powerCheck n p = true ∨ positiveCheck n d p = true := by
    simpa only [positiveCheckCombined, Bool.or_eq_true] using hc
  rcases hh with hp | hb
  · exact powerCheck_sound n p hp x (fun i => (hx i).1)
  · exact positiveCheck_sound n d p hb x hx

theorem affineOuter_sound {n : ℕ} (l w : ℚ) (p : Poly (n+1)) (x : Fin (n+1) → ℝ) :
    eval (affineOuter l w p) x = eval p (Fin.cons ((l : ℝ)+(w : ℝ)*x 0) (fun i => x i.succ)) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    change eval (add [c] (add (scale l (affineOuter l w p)) (zero n :: scale w (affineOuter l w p)))) x = _
    rw [eval_add, eval_add, eval_scale]
    have hc : eval ([c] : Poly (n+1)) x = eval c (fun i => x i.succ) := by
      change eval c (fun i => x i.succ)+x 0*0 = _
      ring
    have hz : eval (zero n :: scale w (affineOuter l w p)) x = x 0*eval (scale w (affineOuter l w p)) x := by
      change eval (zero n) (fun i => x i.succ)+x 0*eval (scale w (affineOuter l w p)) x = _
      rw [eval_zero, zero_add]
    rw [hc, hz, eval_scale, ih]
    change _ = eval c (fun i => x i.succ)+((l : ℝ)+(w : ℝ)*x 0)*eval p (Fin.cons _ _)
    ring

theorem eval_map {n : ℕ} (f : Poly n → Poly n) (p : Poly (n+1))
    (x y : Fin n → ℝ) (t : ℝ) (h : ∀ c, eval (f c) x = eval c y) :
    eval (p.map f) (Fin.cons t x) = eval p (Fin.cons t y) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    change eval (f c) x+t*eval (p.map f) (Fin.cons t x) = eval c y+t*eval p (Fin.cons t y)
    rw [h, ih]

theorem affineAll_sound (n : ℕ) (p : Poly n) (l w : Fin n → ℚ) (x : Fin n → ℝ) :
    eval (affineAll n p l w) x = eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [affineAll, affineOuter_sound]
    rw [eval_map _ p (fun i => x i.succ)
      (fun i => (l i.succ : ℝ)+(w i.succ : ℝ)*x i.succ) _ (fun c => ih c _ _ _)]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem affineCheckFast_sound (n : ℕ) (p a : Poly n) (l w : Fin n → ℚ)
    (h : affineCheckFast n p a l w = true) (x : Fin n → ℝ) :
    eval a x = eval p (fun i => (l i : ℝ)+(w i : ℝ)*x i) := by
  let _ : DecidableEq (Poly n) := polyDecidableEq n
  have he : a = affineAll n p l w := of_decide_eq_true h
  rw [he, affineAll_sound]

theorem box_scaled_margin_fast_sound (n : ℕ) (d : Fin n → ℕ) (u v j a : Poly n)
    (K L s : ℚ) (hK : 0 < K) (l w : Fin n → ℚ)
    (ha : affineCheckFast n (scale K (margin u v j L s)) a l w = true)
    (hb : positiveCheckCombined n d a = true) (x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, x i ∈ Icc (l i : ℝ) ((l i : ℝ)+w i)) :
    0 ≤ eval j x-(L : ℝ)*((1+(s : ℝ))*eval u x+(1+1/(s : ℝ))*eval v x) := by
  let t : Fin n → ℝ := fun i => (x i-(l i : ℝ))/(w i : ℝ)
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hx i).1) hi.le
    · apply (div_le_one hi).mpr
      linarith [(hx i).2]
  have h := positiveCheckCombined_sound n d a hb t ht
  rw [affineCheckFast_sound n _ _ _ _ ha, eval_scale, eval_margin] at h
  have he : (fun i => (l i : ℝ)+(w i : ℝ)*t i) = x := by
    ext i
    have hi : (w i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hw i)
    dsimp [t]
    field_simp
    ring
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hK)

#print axioms affineOuter_sound
#print axioms affineAll_sound
#print axioms affineCheckFast_sound
#print axioms positiveCheckCombined_sound
#print axioms box_scaled_margin_fast_sound
end Gebendorfer.RadenkovicGutman.NestedHorner
