/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectrumRemainders
import Proofs.RadenkovicGutmanClassScalarIntegrals

namespace Gebendorfer.RadenkovicGutman.FiniteSpectrumIntegralRemainders

open Set MeasureTheory
open scoped Classical
noncomputable section

def origin (N B y : ℝ) : ℝ := N * (Real.log y - Real.log (B + 1))
def tail (K y : ℝ) : ℝ := -K / (2 * y ^ 2)

theorem origin_integrable (N B a : ℝ) :
    IntervalIntegrable (origin N B) volume 0 a :=
  (intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_const).const_mul N

theorem origin_integral (N B a : ℝ) :
    (∫ y : ℝ in (0 : ℝ)..a, origin N B y) =
      N * a * (Real.log a - Real.log (B + 1) - 1) := by
  unfold origin
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log' intervalIntegrable_const,
    integral_log_from_zero, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem origin_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (N B a : ℝ) (ha : 0 < a)
    (hb : ∀ y ∈ Ioc (0 : ℝ) a, origin N B y ≤ f y) :
    N * a * (Real.log a - Real.log (B + 1) - 1) ≤
      ∫ y : ℝ in (0 : ℝ)..a, f y := by
  rw [← origin_integral N B a]
  apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le (origin_integrable N B a)
    (TailIntegral.interval_integrable_of_Ioi hf (le_refl 0) ha.le)
  intro y hy
  exact hb y ⟨hy.1,hy.2.le⟩

theorem tail_integrable_integral (K Y : ℝ) (hK : 0 ≤ K) (hY : 0 < Y) :
    IntegrableOn (tail K) (Ioi Y) ∧
      (∫ y : ℝ in Ioi Y, tail K y) = -K / (2 * Y) := by
  obtain ⟨hi,he⟩ := TailIntegral.inv_square_integrable_integral (K / 2) Y (by positivity) hY
  have ht : tail K = (fun y : ℝ => -((K / 2) / y ^ 2)) := by funext y; unfold tail; ring
  constructor
  · rw [ht]
    exact hi.neg
  · rw [ht, integral_neg, he]
    ring

theorem tail_lower (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (K Y : ℝ) (hK : 0 ≤ K) (hY : 0 < Y)
    (hb : ∀ y ∈ Ioi Y, tail K y ≤ f y) :
    -K / (2 * Y) ≤ ∫ y : ℝ in Ioi Y, f y := by
  obtain ⟨hi,he⟩ := tail_integrable_integral K Y hK hY
  rw [← he]
  apply integral_mono_ae hi (hf.mono_set (Ioi_subset_Ioi hY.le))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact hb y hy

variable {V : Type*} [Fintype V]

theorem spectral_origin_integral_lower (a b : V → ℝ) (t B ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : ∀ i, |b i - t| ≤ B) :
    (Fintype.card V : ℝ) * ε * (Real.log ε - Real.log (B + 1) - 1) ≤
      ∫ y : ℝ in (0 : ℝ)..ε, Coulson.logarithm a b t y := by
  apply origin_lower _ (Coulson.logarithm_integrable a b t) _ _ _ hε
  intro y hy
  exact FiniteSpectrumRemainders.spectral_origin_lower a b t y B hy.1 (hy.2.trans hε1) hB

theorem spectral_tail_integral_lower (a b : V → ℝ) (t Y : ℝ) (hY : 0 < Y) :
    -(∑ i, (b i - t) ^ 2) / (2 * Y) ≤
      ∫ y : ℝ in Ioi Y, Coulson.logarithm a b t y := by
  apply tail_lower _ (Coulson.logarithm_integrable a b t) _ _
    (Finset.sum_nonneg (fun i _ => sq_nonneg (b i - t))) hY
  intro y hy
  exact FiniteSpectrumRemainders.spectral_tail_lower a b t y (hY.trans hy)

#print axioms origin_integrable
#print axioms origin_integral
#print axioms origin_lower
#print axioms tail_integrable_integral
#print axioms tail_lower
#print axioms spectral_origin_integral_lower
#print axioms spectral_tail_integral_lower

end
end Gebendorfer.RadenkovicGutman.FiniteSpectrumIntegralRemainders
