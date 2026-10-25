/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01020
import Proofs.RadenkovicGutmanD1Long00Leaf01021
import Proofs.RadenkovicGutmanD1Long00Leaf01022
import Proofs.RadenkovicGutmanD1Long00Leaf01023
import Proofs.RadenkovicGutmanD1Long00Leaf01024
import Proofs.RadenkovicGutmanD1Long00Leaf01025
import Proofs.RadenkovicGutmanD1Long00Leaf01026
import Proofs.RadenkovicGutmanD1Long00Leaf01027
import Proofs.RadenkovicGutmanD1Long00Leaf01028
import Proofs.RadenkovicGutmanD1Long00Leaf01029
import Proofs.RadenkovicGutmanD1Long00Leaf01030
import Proofs.RadenkovicGutmanD1Long00Leaf01031
import Proofs.RadenkovicGutmanD1Long00Leaf01032
import Proofs.RadenkovicGutmanD1Long00Leaf01033
import Proofs.RadenkovicGutmanD1Long00Leaf01034
import Proofs.RadenkovicGutmanD1Long00Leaf01035
import Proofs.RadenkovicGutmanD1Long00Leaf01036
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0060Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf01020) (.leaf DegreeOneLongClass00.leaf01021)) (.leaf DegreeOneLongClass00.leaf01022)) (.leaf DegreeOneLongClass00.leaf01023)) (.leaf DegreeOneLongClass00.leaf01024)) (.leaf DegreeOneLongClass00.leaf01025)) (.leaf DegreeOneLongClass00.leaf01026)) (.leaf DegreeOneLongClass00.leaf01027)) (.leaf DegreeOneLongClass00.leaf01028)) (.leaf DegreeOneLongClass00.leaf01029)) (.leaf DegreeOneLongClass00.leaf01030)) (.leaf DegreeOneLongClass00.leaf01031)) (.leaf DegreeOneLongClass00.leaf01032)) (.leaf DegreeOneLongClass00.leaf01033)) (.leaf DegreeOneLongClass00.leaf01034)) (.leaf DegreeOneLongClass00.leaf01035)) (.leaf DegreeOneLongClass00.leaf01036)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/40),(37/80),(-322679471/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (17/40) (37/80) 0 1 0 1 (-322679471/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf01020_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01021_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01022_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01023_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01024_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01025_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01026_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01027_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01028_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01029_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01030_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01031_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01032_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01033_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01034_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01035_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01036_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((37/80) : ℚ) : ℝ)-(((17/40) : ℚ) : ℝ))*(((-322679471/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/40) : ℚ) : ℝ)..(((37/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0060Complete
