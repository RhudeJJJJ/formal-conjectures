/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00051
import Proofs.RadenkovicGutmanD1Long00Leaf00052
import Proofs.RadenkovicGutmanD1Long00Leaf00053
import Proofs.RadenkovicGutmanD1Long00Leaf00054
import Proofs.RadenkovicGutmanD1Long00Leaf00055
import Proofs.RadenkovicGutmanD1Long00Leaf00056
import Proofs.RadenkovicGutmanD1Long00Leaf00057
import Proofs.RadenkovicGutmanD1Long00Leaf00058
import Proofs.RadenkovicGutmanD1Long00Leaf00059
import Proofs.RadenkovicGutmanD1Long00Leaf00060
import Proofs.RadenkovicGutmanD1Long00Leaf00061
import Proofs.RadenkovicGutmanD1Long00Leaf00062
import Proofs.RadenkovicGutmanD1Long00Leaf00063
import Proofs.RadenkovicGutmanD1Long00Leaf00064
import Proofs.RadenkovicGutmanD1Long00Leaf00065
import Proofs.RadenkovicGutmanD1Long00Leaf00066
import Proofs.RadenkovicGutmanD1Long00Leaf00067
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0003Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00051) (.leaf DegreeOneLongClass00.leaf00052)) (.leaf DegreeOneLongClass00.leaf00053)) (.leaf DegreeOneLongClass00.leaf00054)) (.leaf DegreeOneLongClass00.leaf00055)) (.leaf DegreeOneLongClass00.leaf00056)) (.leaf DegreeOneLongClass00.leaf00057)) (.leaf DegreeOneLongClass00.leaf00058)) (.leaf DegreeOneLongClass00.leaf00059)) (.leaf DegreeOneLongClass00.leaf00060)) (.leaf DegreeOneLongClass00.leaf00061)) (.leaf DegreeOneLongClass00.leaf00062)) (.leaf DegreeOneLongClass00.leaf00063)) (.leaf DegreeOneLongClass00.leaf00064)) (.leaf DegreeOneLongClass00.leaf00065)) (.leaf DegreeOneLongClass00.leaf00066)) (.leaf DegreeOneLongClass00.leaf00067)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/2000),(7/4000),(-21049463197/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/2000) (7/4000) 0 1 0 1 (-21049463197/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00051_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00052_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00053_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00054_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00055_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00056_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00057_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00058_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00059_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00060_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00061_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00062_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00063_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00064_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00065_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00066_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00067_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/4000) : ℚ) : ℝ)-(((3/2000) : ℚ) : ℝ))*(((-21049463197/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/2000) : ℚ) : ℝ)..(((7/4000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0003Complete
