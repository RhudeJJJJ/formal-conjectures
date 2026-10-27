/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperPowerSquareCell0023
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D5UpperPowerSquareCell0023Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .leaf D5UpperPowerSquareCell0023.leaf00023
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(27/3200),(7/800),(-5125783901601593430591/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 5 4 4 (27/3200) (7/800) 0 1 0 1 (-5125783901601593430591/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,decide_eq_true_eq]
  exact ⟨D5UpperPowerSquareCell0023.leaf00023_checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 5 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 5 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=5)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/800) : ℚ) : ℝ)-(((27/3200) : ℚ) : ℝ))*(((-5125783901601593430591/1180591620717411303424) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((27/3200) : ℚ) : ℝ)..(((7/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 5 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D5UpperPowerSquareCell0023Complete
