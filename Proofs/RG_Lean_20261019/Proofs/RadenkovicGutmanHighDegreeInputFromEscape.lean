/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripReserves
import Proofs.RadenkovicGutmanHighDegreeInputFromReserves

/-! Exact original degree-46 target after the full low strips are discharged.
The original correlated-escape signs are the sole remaining sign input. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeInputFromEscape
open Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem normalized_target_of_escape_signs {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 := by
  have hdR : (46 : ℝ) ≤ C.degree u := by exact_mod_cast hd
  apply HighDegreeInputFromReserves.normalized_target_of_reserve_families C u p q hd
  · intro y hy c hc hr
    exact LowStripReserves.tangent_reserve _ _ _ _ _ hdR
      (le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy.1.le))
      (le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy.1.le)) hc hr
  · intro y hy
    have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
    have hcut : (0 : ℝ) < 8/(3*(C.degree u : ℝ)) := by positivity
    have hy0 : 0 < y := lt_of_lt_of_le hcut hy.1
    exact LowStripReserves.constant_reserve _ _ _ _ hdR hy
      (le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy0.le))
      (le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy0.le))
  · exact hEscape

#print axioms normalized_target_of_escape_signs
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeInputFromEscape
