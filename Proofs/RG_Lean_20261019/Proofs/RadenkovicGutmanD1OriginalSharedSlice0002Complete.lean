/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00034
import Proofs.RadenkovicGutmanD1Long00Leaf00035
import Proofs.RadenkovicGutmanD1Long00Leaf00036
import Proofs.RadenkovicGutmanD1Long00Leaf00037
import Proofs.RadenkovicGutmanD1Long00Leaf00038
import Proofs.RadenkovicGutmanD1Long00Leaf00039
import Proofs.RadenkovicGutmanD1Long00Leaf00040
import Proofs.RadenkovicGutmanD1Long00Leaf00041
import Proofs.RadenkovicGutmanD1Long00Leaf00042
import Proofs.RadenkovicGutmanD1Long00Leaf00043
import Proofs.RadenkovicGutmanD1Long00Leaf00044
import Proofs.RadenkovicGutmanD1Long00Leaf00045
import Proofs.RadenkovicGutmanD1Long00Leaf00046
import Proofs.RadenkovicGutmanD1Long00Leaf00047
import Proofs.RadenkovicGutmanD1Long00Leaf00048
import Proofs.RadenkovicGutmanD1Long00Leaf00049
import Proofs.RadenkovicGutmanD1Long00Leaf00050
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0002Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00034) (.leaf DegreeOneLongClass00.leaf00035)) (.leaf DegreeOneLongClass00.leaf00036)) (.leaf DegreeOneLongClass00.leaf00037)) (.leaf DegreeOneLongClass00.leaf00038)) (.leaf DegreeOneLongClass00.leaf00039)) (.leaf DegreeOneLongClass00.leaf00040)) (.leaf DegreeOneLongClass00.leaf00041)) (.leaf DegreeOneLongClass00.leaf00042)) (.leaf DegreeOneLongClass00.leaf00043)) (.leaf DegreeOneLongClass00.leaf00044)) (.leaf DegreeOneLongClass00.leaf00045)) (.leaf DegreeOneLongClass00.leaf00046)) (.leaf DegreeOneLongClass00.leaf00047)) (.leaf DegreeOneLongClass00.leaf00048)) (.leaf DegreeOneLongClass00.leaf00049)) (.leaf DegreeOneLongClass00.leaf00050)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/800),(3/2000),(-21854543295/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/800) (3/2000) 0 1 0 1 (-21854543295/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00034_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00035_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00036_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00037_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00038_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00039_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00040_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00041_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00042_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00043_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00044_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00045_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00046_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00047_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00048_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00049_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00050_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/2000) : ℚ) : ℝ)-(((1/800) : ℚ) : ℝ))*(((-21854543295/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/800) : ℚ) : ℝ)..(((3/2000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0002Complete
