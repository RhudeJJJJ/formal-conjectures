/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01003
import Proofs.RadenkovicGutmanD1Long00Leaf01004
import Proofs.RadenkovicGutmanD1Long00Leaf01005
import Proofs.RadenkovicGutmanD1Long00Leaf01006
import Proofs.RadenkovicGutmanD1Long00Leaf01007
import Proofs.RadenkovicGutmanD1Long00Leaf01008
import Proofs.RadenkovicGutmanD1Long00Leaf01009
import Proofs.RadenkovicGutmanD1Long00Leaf01010
import Proofs.RadenkovicGutmanD1Long00Leaf01011
import Proofs.RadenkovicGutmanD1Long00Leaf01012
import Proofs.RadenkovicGutmanD1Long00Leaf01013
import Proofs.RadenkovicGutmanD1Long00Leaf01014
import Proofs.RadenkovicGutmanD1Long00Leaf01015
import Proofs.RadenkovicGutmanD1Long00Leaf01016
import Proofs.RadenkovicGutmanD1Long00Leaf01017
import Proofs.RadenkovicGutmanD1Long00Leaf01018
import Proofs.RadenkovicGutmanD1Long00Leaf01019
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0059Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf01003) (.leaf DegreeOneLongClass00.leaf01004)) (.leaf DegreeOneLongClass00.leaf01005)) (.leaf DegreeOneLongClass00.leaf01006)) (.leaf DegreeOneLongClass00.leaf01007)) (.leaf DegreeOneLongClass00.leaf01008)) (.leaf DegreeOneLongClass00.leaf01009)) (.leaf DegreeOneLongClass00.leaf01010)) (.leaf DegreeOneLongClass00.leaf01011)) (.leaf DegreeOneLongClass00.leaf01012)) (.leaf DegreeOneLongClass00.leaf01013)) (.leaf DegreeOneLongClass00.leaf01014)) (.leaf DegreeOneLongClass00.leaf01015)) (.leaf DegreeOneLongClass00.leaf01016)) (.leaf DegreeOneLongClass00.leaf01017)) (.leaf DegreeOneLongClass00.leaf01018)) (.leaf DegreeOneLongClass00.leaf01019)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(31/80),(17/40),(-430613781/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (31/80) (17/40) 0 1 0 1 (-430613781/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf01003_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01004_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01005_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01006_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01007_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01008_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01009_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01010_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01011_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01012_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01013_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01014_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01015_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01016_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01017_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01018_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01019_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/40) : ℚ) : ℝ)-(((31/80) : ℚ) : ℝ))*(((-430613781/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((31/80) : ℚ) : ℝ)..(((17/40) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0059Complete
