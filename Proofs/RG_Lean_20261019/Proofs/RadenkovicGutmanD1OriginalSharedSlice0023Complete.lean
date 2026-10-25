/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00391
import Proofs.RadenkovicGutmanD1Long00Leaf00392
import Proofs.RadenkovicGutmanD1Long00Leaf00393
import Proofs.RadenkovicGutmanD1Long00Leaf00394
import Proofs.RadenkovicGutmanD1Long00Leaf00395
import Proofs.RadenkovicGutmanD1Long00Leaf00396
import Proofs.RadenkovicGutmanD1Long00Leaf00397
import Proofs.RadenkovicGutmanD1Long00Leaf00398
import Proofs.RadenkovicGutmanD1Long00Leaf00399
import Proofs.RadenkovicGutmanD1Long00Leaf00400
import Proofs.RadenkovicGutmanD1Long00Leaf00401
import Proofs.RadenkovicGutmanD1Long00Leaf00402
import Proofs.RadenkovicGutmanD1Long00Leaf00403
import Proofs.RadenkovicGutmanD1Long00Leaf00404
import Proofs.RadenkovicGutmanD1Long00Leaf00405
import Proofs.RadenkovicGutmanD1Long00Leaf00406
import Proofs.RadenkovicGutmanD1Long00Leaf00407
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0023Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00391) (.leaf DegreeOneLongClass00.leaf00392)) (.leaf DegreeOneLongClass00.leaf00393)) (.leaf DegreeOneLongClass00.leaf00394)) (.leaf DegreeOneLongClass00.leaf00395)) (.leaf DegreeOneLongClass00.leaf00396)) (.leaf DegreeOneLongClass00.leaf00397)) (.leaf DegreeOneLongClass00.leaf00398)) (.leaf DegreeOneLongClass00.leaf00399)) (.leaf DegreeOneLongClass00.leaf00400)) (.leaf DegreeOneLongClass00.leaf00401)) (.leaf DegreeOneLongClass00.leaf00402)) (.leaf DegreeOneLongClass00.leaf00403)) (.leaf DegreeOneLongClass00.leaf00404)) (.leaf DegreeOneLongClass00.leaf00405)) (.leaf DegreeOneLongClass00.leaf00406)) (.leaf DegreeOneLongClass00.leaf00407)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/320),(1/100),(-3287375087/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/320) (1/100) 0 1 0 1 (-3287375087/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00391_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00392_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00393_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00394_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00395_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00396_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00397_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00398_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00399_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00400_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00401_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00402_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00403_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00404_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00405_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00406_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00407_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/100) : ℚ) : ℝ)-(((3/320) : ℚ) : ℝ))*(((-3287375087/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/320) : ℚ) : ℝ)..(((1/100) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0023Complete
