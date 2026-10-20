/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualFusionIntegral
import Proofs.RadenkovicGutmanConcreteGraphQuotient
import Proofs.RadenkovicGutmanArmClasses

/-!
# Fifteen-class bounds for the same actual source/fused integral

One fixed unordered class pair is selected by the two physical arm lengths.
Its own lower function is integrated. No pointwise minimum across distinct
class payments is substituted. The sign certificates remain explicit inputs.
-/
namespace Gebendorfer.RadenkovicGutman.ClassEnvelope
open CoreQuotient ArmClasses Focus Set MeasureTheory ActualFusionIntegral
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def pair (p q : ℕ) : Fin 5 × Fin 5 :=
  if classify p ≤ classify q then (classify p, classify q) else (classify q, classify p)

theorem pair_mem (p q : ℕ) : pair p q ∈ unordered := by
  by_cases h : classify p ≤ classify q
  · simp [pair, h, unordered]
  · simp [pair, h, unordered, le_of_not_ge h]

def Bounds (d : ℕ) (B : (Fin 5 × Fin 5) → ℝ → ℝ) : Prop :=
  ∀ c ∈ unordered, ∀ y : ℝ, 0 < y →
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ ζ : ℂ,
      ‖ζ - g d y‖ ≤ r d y →
        B c y ≤ Real.log ‖quotient y (parameter y c.1 s) (parameter y c.2 t) ζ‖

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_lower (C : SimpleGraph V) (u : V) (p q d : ℕ)
    (hd : C.degree u = d) (B : (Fin 5 × Fin 5) → ℝ → ℝ) (hB : Bounds d B)
    (y : ℝ) (hy : 0 < y) :
    B (pair p q) y ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  obtain ⟨s, hs, hp⟩ := actual_parameter y hy p
  obtain ⟨t, ht, hq⟩ := actual_parameter y hy q
  have hζ := (schur_in_disk C u y hy).1
  rw [hd] at hζ
  change B (pair p q) y ≤ Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy p q, hp, hq]
  by_cases h : classify p ≤ classify q
  · simpa only [pair, if_pos h] using
      hB (classify p, classify q) (by simp [unordered, h]) y hy s hs t ht _ hζ
  · have hb := hB (classify q, classify p) (by simp [unordered, le_of_not_ge h])
      y hy t ht s hs _ hζ
    rw [quotient_swap] at hb
    simpa only [pair, if_neg h] using hb

theorem integral_lower (C : SimpleGraph V) (u : V) (p q d : ℕ)
    (hd : C.degree u = d) (B : (Fin 5 × Fin 5) → ℝ → ℝ) (hB : Bounds d B)
    (hBi : ∀ c ∈ unordered, IntegrableOn (B c) (Ioi 0)) :
    (1 / Real.pi) * (∫ y : ℝ in Ioi 0, B (pair p q) y) ≤
      normalizedIntegral C u p q 2 := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (hBi _ (pair_mem p q)) (logarithm_integrable C u p q 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact graph_lower C u p q d hd B hB y hy

#check @Bounds
#print axioms pair_mem
#print axioms graph_lower
#print axioms integral_lower
end
end Gebendorfer.RadenkovicGutman.ClassEnvelope
