/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01737
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0105Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .leaf DegreeOneLongClass00.leaf01737
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(256/13),(64/3),(142561/67108864)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (256/13) (64/3) 0 1 0 1 (142561/67108864) cover=true := by
  simp only [cover,FastArmCover.accepts,decide_eq_true_eq]
  exact ⟨DegreeOneLongClass00.leaf01737_checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/3) : ℚ) : ℝ)-(((256/13) : ℚ) : ℝ))*(((142561/67108864) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((256/13) : ℚ) : ℝ)..(((64/3) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0105Complete
