/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedHorner

namespace Gebendorfer.RadenkovicGutman.NestedPositiveScale
open NestedHorner
set_option maxHeartbeats 0

theorem scale_add (n : ℕ) (c : ℚ) (p q : Poly n) :
    scale c (add p q)=add (scale c p) (scale c q) := by
  induction n with
  | zero => simp only [scale,add]; ring
  | succ n ih =>
    induction p generalizing q with
    | nil => rfl
    | cons a p hp =>
      cases q with
      | nil => rfl
      | cons b q =>
        simp only [scale,add,zipAdd,List.map_cons]
        rw [ih]
        congr 1
        exact hp q

theorem scale_scale (n : ℕ) (c d : ℚ) (p : Poly n) :
    scale c (scale d p)=scale (c*d) p := by
  induction n with
  | zero => simp only [scale]; ring
  | succ n ih =>
    induction p with
    | nil => rfl
    | cons a p hp =>
      simp only [scale,List.map_cons]
      rw [ih]
      congr 1

theorem scale_zero (n : ℕ) (c : ℚ) : scale c (zero n)=zero n := by
  cases n <;> simp [zero,scale]

theorem coefficientFrom_scale {n : ℕ} (D j k : ℕ) (c : ℚ) (p : Poly (n+1)) :
    coefficientFrom D j k (scale c p)=scale c (coefficientFrom D j k p) := by
  induction p generalizing k with
  | nil => simp [scale,coefficientFrom,scale_zero]
  | cons a p hp =>
    simp only [scale] at hp
    simp only [scale,List.map_cons,coefficientFrom]
    rw [scale_add,hp]
    by_cases h : k ≤ j
    · simp only [if_pos h,scale_scale]
      rw [mul_comm (Nat.fast_choose (D-k) (j-k) : ℚ) c]
    · simp only [if_neg h,scale_zero]

theorem positiveCheck_scale (n : ℕ) (d : Fin n → ℕ) (p : Poly n)
    (c : ℚ) (hc : 0 ≤ c) (hp : positiveCheck n d p=true) :
    positiveCheck n d (scale c p)=true := by
  induction n with
  | zero =>
    apply decide_eq_true
    exact mul_nonneg hc (of_decide_eq_true hp)
  | succ n ih =>
    obtain ⟨hlen,hcoeff⟩ := of_decide_eq_true hp
    apply decide_eq_true
    refine ⟨by simpa only [scale,List.length_map] using hlen,?_⟩
    intro j
    rw [coefficientFrom_scale]
    exact ih _ _ (hcoeff j)

#print axioms coefficientFrom_scale
#print axioms positiveCheck_scale
end Gebendorfer.RadenkovicGutman.NestedPositiveScale
