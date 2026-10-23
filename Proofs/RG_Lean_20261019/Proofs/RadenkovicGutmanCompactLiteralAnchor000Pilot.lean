/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCompactLiteralAnchor000Base
import Proofs.RadenkovicGutmanCompactAnchor000Cell000
namespace Gebendorfer.RadenkovicGutman.CompactLiteralAnchor000Pilot
open Set MeasureTheory
open CompactLiteralAnchor000Base
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
abbrev witness := CompactAnchor000Cell000.witness
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.actual_integral_lower (51/26) 9 9 data path_checked norms_checked witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactLiteralAnchor000Pilot
