/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exact affine substitution with integer denominator clearing at every coordinate.
The checker never approximates, truncates, or samples a polynomial.
-/
import Proofs.RadenkovicGutmanNestedInteger
namespace Gebendorfer.RadenkovicGutman.NestedInteger
open Set
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def clearedOuter {n : ℕ} (l w D : ℤ) : Poly (n+1) → Poly (n+1)
  | [] => []
  | c :: p =>
    let q := clearedOuter l w D p
    add [scale (D^p.length) c] (add (scale l q) (zero n :: scale w q))
def clearedAll : (n : ℕ) → Poly n → (Fin n → ℤ) → (Fin n → ℤ) → (Fin n → ℤ) → Poly n
  | 0, p, _, _, _ => p
  | n+1, p, l, w, D => clearedOuter (l 0) (w 0) (D 0)
      (p.map (fun c => clearedAll n c (fun i => l i.succ) (fun i => w i.succ) (fun i => D i.succ)))
def rectangular : (n : ℕ) → (Fin n → ℕ) → Poly n → Bool
  | 0, _, _ => true
  | n+1, d, p => decide (p.length=d 0+1) && p.all (rectangular n (fun i => d i.succ))
def factor : (n : ℕ) → (Fin n → ℕ) → (Fin n → ℤ) → ℤ
  | 0, _, _ => 1
  | n+1, d, D => D 0 ^ d 0 * factor n (fun i => d i.succ) (fun i => D i.succ)

theorem factor_pos (n : ℕ) (d : Fin n → ℕ) (D : Fin n → ℤ) (hD : ∀ i, 0 < D i) :
    0 < factor n d D := by
  induction n with
  | zero => exact Int.zero_lt_one
  | succ n ih => exact mul_pos (pow_pos (hD 0) _) (ih _ _ (fun i => hD i.succ))

theorem clearedOuter_cons {n : ℕ} (l w D : ℤ) (c : Poly n) (p : Poly (n+1)) (x : Fin (n+1) → ℝ) :
    NestedHorner.eval (castPoly (n+1) (clearedOuter l w D (c::p))) x =
      (D : ℝ)^p.length*NestedHorner.eval (castPoly n c) (fun i => x i.succ)+
      ((l : ℝ)+(w : ℝ)*x 0)*NestedHorner.eval (castPoly (n+1) (clearedOuter l w D p)) x := by
  change NestedHorner.eval (castPoly (n+1) (add [scale (D^p.length) c]
    (add (scale l (clearedOuter l w D p)) (zero n :: scale w (clearedOuter l w D p))))) x = _
  rw [cast_add, cast_add, NestedHorner.eval_add, NestedHorner.eval_add, cast_scale, NestedHorner.eval_scale]
  change NestedHorner.eval (castPoly n (scale (D^p.length) c)) (fun i => x i.succ)+x 0*0+
    (((l : ℚ) : ℝ)*NestedHorner.eval (castPoly (n+1) (clearedOuter l w D p)) x+
    (NestedHorner.eval (castPoly n (zero n)) (fun i => x i.succ)+
      x 0*NestedHorner.eval (castPoly (n+1) (scale w (clearedOuter l w D p))) x)) = _
  rw [cast_scale, cast_scale, cast_zero, NestedHorner.eval_zero, NestedHorner.eval_scale, NestedHorner.eval_scale]
  push_cast
  ring

theorem clearedOuter_sound {n : ℕ} (l w D : ℤ) (p : Poly (n+1)) (x : Fin (n+1) → ℝ) (hD : D ≠ 0) :
    (D : ℝ)*NestedHorner.eval (castPoly (n+1) (clearedOuter l w D p)) x =
      (D : ℝ)^p.length*NestedHorner.eval (castPoly (n+1) p)
        (Fin.cons (((l : ℝ)+(w : ℝ)*x 0)/(D : ℝ)) (fun i => x i.succ)) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  induction p with
  | nil => change (D : ℝ)*0=(D : ℝ)^0*0; ring
  | cons c p ih =>
    rw [clearedOuter_cons]
    change (D : ℝ)*((D : ℝ)^p.length*NestedHorner.eval (castPoly n c) (fun i => x i.succ)+
      ((l : ℝ)+(w : ℝ)*x 0)*NestedHorner.eval (castPoly (n+1) (clearedOuter l w D p)) x) =
      (D : ℝ)^(p.length+1)*(NestedHorner.eval (castPoly n c) (fun i => x i.succ)+
        (((l : ℝ)+(w : ℝ)*x 0)/(D : ℝ))*NestedHorner.eval (castPoly (n+1) p) (Fin.cons _ _))
    calc
      _ = (D : ℝ)^p.length*(D : ℝ)*NestedHorner.eval (castPoly n c) (fun i => x i.succ)+
          ((l : ℝ)+(w : ℝ)*x 0)*((D : ℝ)*NestedHorner.eval (castPoly (n+1) (clearedOuter l w D p)) x) := by ring
      _ = _ := by rw [ih, pow_succ]; field_simp

theorem eval_map_scaled {n : ℕ} (f : Poly n → Poly n) (p : Poly (n+1))
    (x y : Fin n → ℝ) (t K : ℝ)
    (h : ∀ c ∈ p, NestedHorner.eval (castPoly n (f c)) x=K*NestedHorner.eval (castPoly n c) y) :
    NestedHorner.eval (castPoly (n+1) (p.map f)) (Fin.cons t x) =
      K*NestedHorner.eval (castPoly (n+1) p) (Fin.cons t y) := by
  induction p with
  | nil => change 0=K*0; ring
  | cons c p ih =>
    have hc := h c (by simp)
    have hp := ih (fun c hc => h c (by simp [hc]))
    change NestedHorner.eval (castPoly n (f c)) x+t*NestedHorner.eval (castPoly (n+1) (p.map f)) (Fin.cons t x) =
      K*(NestedHorner.eval (castPoly n c) y+t*NestedHorner.eval (castPoly (n+1) p) (Fin.cons t y))
    rw [hc,hp]
    ring

theorem clearedAll_sound (n : ℕ) (d : Fin n → ℕ) (p : Poly n) (l w D : Fin n → ℤ)
    (hr : rectangular n d p=true) (hD : ∀ i, D i ≠ 0) (x : Fin n → ℝ) :
    NestedHorner.eval (castPoly n (clearedAll n p l w D)) x =
      (factor n d D : ℝ)*NestedHorner.eval (castPoly n p)
        (fun i => ((l i : ℝ)+(w i : ℝ)*x i)/(D i : ℝ)) := by
  induction n with
  | zero => simp [clearedAll, factor, castPoly, NestedHorner.eval]
  | succ n ih =>
    have hb : decide (p.length=d 0+1)=true ∧ p.all (rectangular n (fun i => d i.succ))=true := by
      simpa only [rectangular, Bool.and_eq_true] using hr
    have hlen : p.length=d 0+1 := of_decide_eq_true hb.1
    have hs : ∀ c ∈ p, rectangular n (fun i => d i.succ) c=true := by
      simpa only [List.all_eq_true] using hb.2
    let f := fun c => clearedAll n c (fun i => l i.succ) (fun i => w i.succ) (fun i => D i.succ)
    have h := clearedOuter_sound (l 0) (w 0) (D 0) (p.map f) x (hD 0)
    rw [List.length_map, hlen, pow_succ] at h
    have hD0 : (D 0 : ℝ) ≠ 0 := by exact_mod_cast hD 0
    have he : NestedHorner.eval (castPoly (n+1) (clearedAll (n+1) p l w D)) x =
        (D 0 : ℝ)^d 0*NestedHorner.eval (castPoly (n+1) (p.map f))
          (Fin.cons (((l 0 : ℝ)+(w 0 : ℝ)*x 0)/(D 0 : ℝ)) (fun i => x i.succ)) := by
      apply (mul_left_cancel₀ hD0)
      change (D 0 : ℝ)*NestedHorner.eval (castPoly (n+1) (clearedOuter (l 0) (w 0) (D 0) (p.map f))) x = _
      rw [h]
      ring
    rw [he, eval_map_scaled f p _ _ _ (factor n (fun i => d i.succ) (fun i => D i.succ) : ℝ)
      (fun c hc => ih _ c _ _ _ (hs c hc) (fun i => hD i.succ) _)]
    simp only [factor, Int.cast_mul, Int.cast_pow]
    rw [mul_assoc]
    congr 2

theorem box_cleared_margin_sound (n : ℕ) (d : Fin n → ℕ) (u v j : NestedHorner.Poly n) (a raw : Poly n)
    (K L s : ℚ) (hK : 0 < K) (l w D : Fin n → ℤ)
    (hraw : castPoly n raw=NestedHorner.scale K (NestedHorner.margin u v j L s))
    (hr : rectangular n d raw=true) (ha : a=clearedAll n raw l w D)
    (hb : accepts n d a=true) (x : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hD : ∀ i, 0 < D i)
    (hx : ∀ i, x i ∈ Icc ((l i : ℝ)/(D i : ℝ)) (((l i : ℝ)+(w i : ℝ))/(D i : ℝ))) :
    0 ≤ NestedHorner.eval j x-(L : ℝ)*((1+(s : ℝ))*NestedHorner.eval u x+(1+1/(s : ℝ))*NestedHorner.eval v x) := by
  let t : Fin n → ℝ := fun i => ((D i : ℝ)*x i-(l i : ℝ))/(w i : ℝ)
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hw0 : (0 : ℝ) < w i := by exact_mod_cast hw i
    have hD0 : (0 : ℝ) < D i := by exact_mod_cast hD i
    have hl := (div_le_iff₀ hD0).mp (hx i).1
    have hu := (le_div_iff₀ hD0).mp (hx i).2
    constructor
    · apply div_nonneg _ hw0.le
      nlinarith
    · apply (div_le_one hw0).mpr
      nlinarith
  have he := clearedAll_sound n d raw l w D hr (fun i => (hD i).ne') t
  rw [← ha] at he
  have h := accepts_sound n d a hb t ht
  rw [he] at h
  have hvec : (fun i => ((l i : ℝ)+(w i : ℝ)*t i)/(D i : ℝ))=x := by
    ext i
    have hwi : (w i : ℝ) ≠ 0 := by exact_mod_cast (hw i).ne'
    have hDi : (D i : ℝ) ≠ 0 := by exact_mod_cast (hD i).ne'
    dsimp [t]
    field_simp
    ring
  rw [hvec,hraw,NestedHorner.eval_scale,NestedHorner.eval_margin] at h
  have hfactor : (0 : ℝ) < factor n d D := by exact_mod_cast factor_pos n d D hD
  exact nonneg_of_mul_nonneg_right (nonneg_of_mul_nonneg_right h hfactor) (by exact_mod_cast hK)

#print axioms clearedOuter_sound
#print axioms clearedAll_sound
#print axioms box_cleared_margin_sound
end Gebendorfer.RadenkovicGutman.NestedInteger
