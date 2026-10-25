/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2PowerParameterGroup0001
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D2PowerParameterGroup0001Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .leaf D2PowerParameterGroup0001.leaf00005
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(33/32000),(17/16000),(-32262482689769536689873/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (33/32000) (17/16000) 0 1 0 1 (-32262482689769536689873/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,decide_eq_true_eq]
  exact ⟨D2PowerParameterGroup0001.leaf00005_checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=2)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/16000) : ℚ) : ℝ)-(((33/32000) : ℚ) : ℝ))*(((-32262482689769536689873/4722366482869645213696) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((33/32000) : ℚ) : ℝ)..(((17/16000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 2 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D2PowerParameterGroup0001Complete
