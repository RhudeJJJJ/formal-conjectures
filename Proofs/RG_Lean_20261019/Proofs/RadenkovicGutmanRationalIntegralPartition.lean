/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailIntegral

namespace Gebendorfer.RadenkovicGutman.RationalIntegralPartition
open Set MeasureTheory

structure Slice where
  a : ℚ
  b : ℚ
  payment : ℚ

def check : ℚ → ℚ → List Slice → Bool
  | a, b, [] => decide (a=b)
  | a, b, c :: cs => decide (c.a=a ∧ c.a≤c.b) && check c.b b cs

def total : List Slice → ℚ
  | [] => 0
  | c :: cs => c.payment+total cs

theorem order (a b : ℚ) (cs : List Slice) (hc : check a b cs = true) : a ≤ b := by
  induction cs generalizing a with
  | nil => exact (of_decide_eq_true hc).le
  | cons c cs ih =>
      have h : decide (c.a=a ∧ c.a≤c.b) = true ∧ check c.b b cs = true :=
        by simpa only [check,Bool.and_eq_true] using hc
      obtain ⟨he,hb⟩ := of_decide_eq_true h.1
      rw [← he]
      exact hb.trans (ih c.b h.2)

noncomputable section

/-- Checked adjacency and proved payments cover the entire closed interval. -/
theorem integral_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (a b : ℚ) (cs : List Slice) (ha : 0 ≤ a) (hc : check a b cs = true)
    (hp : ∀ c ∈ cs, (c.payment : ℝ) ≤ ∫ y : ℝ in (c.a : ℝ)..(c.b : ℝ), f y) :
    (total cs : ℝ) ≤ ∫ y : ℝ in (a : ℝ)..(b : ℝ), f y := by
  induction cs generalizing a with
  | nil =>
      have he : a=b := of_decide_eq_true hc
      subst b
      simp [total]
  | cons c cs ih =>
      have h : decide (c.a=a ∧ c.a≤c.b) = true ∧ check c.b b cs = true :=
        by simpa only [check,Bool.and_eq_true] using hc
      obtain ⟨he,hab⟩ := of_decide_eq_true h.1
      have hcb : a ≤ c.b := by simpa [he] using hab
      have hcb0 : 0 ≤ c.b := ha.trans hcb
      have hrest := ih c.b hcb0 h.2 (fun d hd => hp d (by simp [hd]))
      have hfirst := hp c (by simp)
      rw [he] at hfirst
      have hi0 := TailIntegral.interval_integrable_of_Ioi hf
        (a := (a : ℝ)) (b := (c.b : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hcb)
      have hi1 := TailIntegral.interval_integrable_of_Ioi hf
        (a := (c.b : ℝ)) (b := (b : ℝ)) (by exact_mod_cast hcb0)
        (by exact_mod_cast order c.b b cs h.2)
      calc
        (total (c :: cs) : ℝ) = (c.payment : ℝ)+(total cs : ℝ) := by simp [total]
        _ ≤ (∫ y : ℝ in (a : ℝ)..(c.b : ℝ), f y)+
          (∫ y : ℝ in (c.b : ℝ)..(b : ℝ), f y) := add_le_add hfirst hrest
        _ = _ := intervalIntegral.integral_add_adjacent_intervals hi0 hi1

theorem three_region_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (a Y O B T : ℝ) (ha : 0 ≤ a) (haY : a ≤ Y)
    (ho : O ≤ ∫ y : ℝ in (0 : ℝ)..a, f y)
    (hb : B ≤ ∫ y : ℝ in a..Y, f y)
    (ht : T ≤ ∫ y : ℝ in Ioi Y, f y) :
    O+B+T ≤ ∫ y : ℝ in Ioi 0, f y := by
  have h0 := intervalIntegral.integral_Ioi_sub_Ioi hf ha
  have h1 := intervalIntegral.integral_Ioi_sub_Ioi (hf.mono_set (Ioi_subset_Ioi ha)) haY
  linarith only [ho,hb,ht,h0,h1]

#print axioms order
#print axioms integral_lower
#print axioms three_region_lower
end
end Gebendorfer.RadenkovicGutman.RationalIntegralPartition
