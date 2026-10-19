/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Integer-only Bernstein arithmetic after exact positive denominator clearing.
Its acceptance theorem is reduced to the proved rational checker.
-/
import Proofs.RadenkovicGutmanNestedHornerTransform
namespace Gebendorfer.RadenkovicGutman.NestedInteger
open Set
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
abbrev Poly : ℕ → Type
  | 0 => ℤ
  | n+1 => List (Poly n)
def zero : (n : ℕ) → Poly n
  | 0 => 0
  | _+1 => []
def add : {n : ℕ} → Poly n → Poly n → Poly n
  | 0, p, q => p+q
  | _+1, p, q => NestedHorner.zipAdd add p q
def scale (c : ℤ) : {n : ℕ} → Poly n → Poly n
  | 0, p => c*p
  | _+1, p => p.map (scale c)
def castPoly : (n : ℕ) → Poly n → NestedHorner.Poly n
  | 0, p => (p : ℚ)
  | n+1, p => p.map (castPoly n)

theorem cast_zero (n : ℕ) : castPoly n (zero n) = NestedHorner.zero n := by
  cases n <;> simp [castPoly, zero, NestedHorner.zero]
theorem cast_add {n : ℕ} (p q : Poly n) :
    castPoly n (add p q) = NestedHorner.add (castPoly n p) (castPoly n q) := by
  induction n with
  | zero => simp [castPoly, add, NestedHorner.add]
  | succ n ih =>
    induction p generalizing q with
    | nil => simp [castPoly, add, NestedHorner.add, NestedHorner.zipAdd]
    | cons c p hp =>
      cases q with
      | nil => simp [castPoly, add, NestedHorner.add, NestedHorner.zipAdd]
      | cons d q =>
        change castPoly n (add c d) :: castPoly (n+1) (add p q) =
          NestedHorner.add (castPoly n c) (castPoly n d) :: NestedHorner.add (castPoly (n+1) p) (castPoly (n+1) q)
        rw [ih, hp]
theorem cast_scale (c : ℤ) {n : ℕ} (p : Poly n) :
    castPoly n (scale c p) = NestedHorner.scale (c : ℚ) (castPoly n p) := by
  induction n with
  | zero => simp [castPoly, scale, NestedHorner.scale]
  | succ n ih =>
    induction p with
    | nil => rfl
    | cons d p hp =>
      change castPoly n (scale c d) :: castPoly (n+1) (scale c p) =
        NestedHorner.scale (c : ℚ) (castPoly n d) :: NestedHorner.scale (c : ℚ) (castPoly (n+1) p)
      rw [ih, hp]

def coefficientFrom {n : ℕ} (D j : ℕ) : ℕ → Poly (n+1) → Poly n
  | _, [] => zero n
  | k, c :: p => add (if k ≤ j then scale (Nat.fast_choose (D-k) (j-k)) c else zero n)
      (coefficientFrom D j (k+1) p)
theorem cast_coefficientFrom {n : ℕ} (D j k : ℕ) (p : Poly (n+1)) :
    castPoly n (coefficientFrom D j k p) = NestedHorner.coefficientFrom D j k (castPoly (n+1) p) := by
  induction p generalizing k with
  | nil => simp [coefficientFrom, castPoly, NestedHorner.coefficientFrom, cast_zero]
  | cons c p ih =>
    by_cases h : k ≤ j
    · simp only [coefficientFrom, castPoly, List.map_cons, NestedHorner.coefficientFrom, if_pos h,
        cast_add, cast_scale, Int.cast_natCast, ih]
    · simp only [coefficientFrom, castPoly, List.map_cons, NestedHorner.coefficientFrom, if_neg h,
        cast_add, cast_zero, ih]

def bernsteinCheck : (n : ℕ) → (Fin n → ℕ) → Poly n → Bool
  | 0, _, p => decide (0 ≤ p)
  | n+1, d, p => decide (p.length ≤ d 0+1 ∧
      ∀ j : Fin (d 0+1), bernsteinCheck n (fun i => d i.succ) (coefficientFrom (d 0) j.val 0 p) = true)
def powerCheck : (n : ℕ) → Poly n → Bool
  | 0, p => decide (0 ≤ p)
  | n+1, p => p.all (powerCheck n)
def accepts (n : ℕ) (d : Fin n → ℕ) (p : Poly n) : Bool := powerCheck n p || bernsteinCheck n d p

theorem bernsteinCheck_to_rational (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (hc : bernsteinCheck n d p = true) : NestedHorner.positiveCheck n d (castPoly n p) = true := by
  induction n with
  | zero =>
    apply decide_eq_true
    change (0 : ℚ) ≤ (p : ℚ)
    exact_mod_cast (of_decide_eq_true hc : (0 : ℤ) ≤ p)
  | succ n ih =>
    obtain ⟨hp, hs⟩ := of_decide_eq_true hc
    apply decide_eq_true
    refine ⟨by simpa only [castPoly, List.length_map] using hp, ?_⟩
    intro j
    have h := ih _ _ (hs j)
    rwa [cast_coefficientFrom] at h

theorem powerCheck_sound (n : ℕ) (p : Poly n) (hc : powerCheck n p = true)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ NestedHorner.eval (castPoly n p) x := by
  induction n with
  | zero =>
    change (0 : ℝ) ≤ ((p : ℚ) : ℝ)
    exact_mod_cast (of_decide_eq_true hc : (0 : ℤ) ≤ p)
  | succ n ih =>
    induction p with
    | nil => exact le_rfl
    | cons c p hp =>
      have hh : powerCheck n c = true ∧ p.all (powerCheck n) = true := by
        simpa only [powerCheck, List.all_cons, Bool.and_eq_true] using hc
      change 0 ≤ NestedHorner.eval (castPoly n c) (fun i => x i.succ)+x 0*NestedHorner.eval (castPoly (n+1) p) x
      exact add_nonneg (ih c hh.1 _ (fun i => hx i.succ)) (mul_nonneg (hx 0) (hp hh.2))

theorem accepts_sound (n : ℕ) (d : Fin n → ℕ) (p : Poly n) (hc : accepts n d p = true)
    (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) : 0 ≤ NestedHorner.eval (castPoly n p) x := by
  have hh : powerCheck n p = true ∨ bernsteinCheck n d p = true := by simpa only [accepts, Bool.or_eq_true] using hc
  rcases hh with hp | hb
  · exact powerCheck_sound n p hp x (fun i => (hx i).1)
  · exact NestedHorner.positiveCheck_sound n d _ (bernsteinCheck_to_rational n d p hb) x hx

theorem box_scaled_margin_sound (n : ℕ) (d : Fin n → ℕ) (u v j : NestedHorner.Poly n) (a : Poly n)
    (K L s : ℚ) (hK : 0 < K) (l w : Fin n → ℚ)
    (ha : NestedHorner.affineCheckFast n (NestedHorner.scale K (NestedHorner.margin u v j L s)) (castPoly n a) l w = true)
    (hb : accepts n d a = true) (x : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hx : ∀ i, x i ∈ Icc (l i : ℝ) ((l i : ℝ)+w i)) :
    0 ≤ NestedHorner.eval j x-(L : ℝ)*((1+(s : ℝ))*NestedHorner.eval u x+(1+1/(s : ℝ))*NestedHorner.eval v x) := by
  let t : Fin n → ℝ := fun i => (x i-(l i : ℝ))/(w i : ℝ)
  have ht : ∀ i, t i ∈ Icc (0 : ℝ) 1 := by
    intro i
    have hi : (0 : ℝ) < w i := by exact_mod_cast hw i
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hx i).1) hi.le
    · apply (div_le_one hi).mpr
      linarith [(hx i).2]
  have h := accepts_sound n d a hb t ht
  rw [NestedHorner.affineCheckFast_sound n _ _ _ _ ha, NestedHorner.eval_scale, NestedHorner.eval_margin] at h
  have he : (fun i => (l i : ℝ)+(w i : ℝ)*t i) = x := by
    ext i
    have hi : (w i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hw i)
    dsimp [t]
    field_simp
    ring
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hK)

#print axioms cast_coefficientFrom
#print axioms bernsteinCheck_to_rational
#print axioms accepts_sound
#print axioms box_scaled_margin_sound
end Gebendorfer.RadenkovicGutman.NestedInteger
