/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClassGraphRemainders
import Proofs.RadenkovicGutmanArmClasses

namespace Gebendorfer.RadenkovicGutman.ActualArmSymmetry
open MeasureTheory Set ActualFusionIntegral ClassGraphRemainders
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- Swapping the actual pendant arms preserves the normalized integral at two. -/
theorem normalized_swap_two {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) :
    normalizedIntegral C u p q 2 = normalizedIntegral C u q p 2 := by
  unfold normalizedIntegral
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  rw [actual_logarithm C u p q y hy,actual_logarithm C u q p y hy,
    ArmClasses.quotient_swap]

#print axioms normalized_swap_two
end
end Gebendorfer.RadenkovicGutman.ActualArmSymmetry
