/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Exhaustive five-class parameterization of all positive arm lengths.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, five-class recurrence enclosure.
-/
import Proofs.RadenkovicGutmanArmBridge
import Proofs.RadenkovicGutmanFocus

namespace Gebendorfer.RadenkovicGutman.ArmClasses
open PathEnclosure Set
open scoped Classical
noncomputable section

/-- The recurrence index is one less than the physical arm length. -/
def classify (n : ℕ) : Fin 5 := ⟨min n 4, by omega⟩

def parameter (y : ℝ) (c : Fin 5) (t : ℝ) : ℝ :=
  if c.val < 4 then rho y c.val
  else y + (lower y + t * (upper y - lower y)) / y

theorem long_width_pos (y : ℝ) (hy : 0 < y) : 0 < upper y - lower y := by
  rw [interval_width y hy]
  positivity

theorem actual_parameter (y : ℝ) (hy : 0 < y) (n : ℕ) :
    ∃ t ∈ Icc (0 : ℝ) 1, rho y n = parameter y (classify n) t := by
  by_cases hn : n < 4
  · refine ⟨0, by norm_num, ?_⟩
    simp only [parameter, classify, Fin.val_mk, Nat.min_eq_left hn.le, hn, ↓reduceIte]
  · have hn4 : 4 ≤ n := by omega
    have hlong := all_long_arms y hy (n - 4)
    have he : n - 4 + 4 = n := by omega
    rw [he] at hlong
    have hw := long_width_pos y hy
    let t := (arm y n - lower y) / (upper y - lower y)
    refine ⟨t, ?_, ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr hlong.1) hw.le
      · apply (div_le_one hw).mpr
        linarith [hlong.2]
    · simp only [parameter, classify, Fin.val_mk, Nat.min_eq_right hn4,
        show ¬ (4 : ℕ) < 4 by omega, ↓reduceIte, rho]
      congr 2
      dsimp [t]
      field_simp
      ring

def unordered : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter (fun c => c.1 ≤ c.2)

theorem unordered_card : unordered.card = 15 := by decide +kernel

/-- This is an exhaustive reduction, not a count of sampled lengths. -/
theorem all_pairs (y : ℝ) (hy : 0 < y) (R : ℝ → ℝ → Prop)
    (hsym : ∀ P Q, R P Q → R Q P)
    (hclasses : ∀ c ∈ unordered, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      R (parameter y c.1 s) (parameter y c.2 t)) (p q : ℕ) :
    R (rho y p) (rho y q) := by
  obtain ⟨s, hs, hp⟩ := actual_parameter y hy p
  obtain ⟨t, ht, hq⟩ := actual_parameter y hy q
  rw [hp, hq]
  by_cases h : classify p ≤ classify q
  · exact hclasses (classify p, classify q) (by simp [unordered, h]) s hs t ht
  · apply hsym
    exact hclasses (classify q, classify p) (by simp [unordered, le_of_not_ge h]) t ht s hs

theorem quotient_swap (y P Q : ℝ) (ζ : ℂ) :
    Focus.quotient y P Q ζ = Focus.quotient y Q P ζ := by
  unfold Focus.quotient Focus.A Focus.N₀ Focus.B Focus.D₀
  rw [mul_comm P Q, add_comm P Q]

#print axioms actual_parameter
#print axioms unordered_card
#print axioms all_pairs
#print axioms quotient_swap
end
end Gebendorfer.RadenkovicGutman.ArmClasses
