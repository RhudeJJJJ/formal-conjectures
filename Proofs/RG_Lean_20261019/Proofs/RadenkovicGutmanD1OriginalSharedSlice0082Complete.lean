/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01394
import Proofs.RadenkovicGutmanD1Long00Leaf01395
import Proofs.RadenkovicGutmanD1Long00Leaf01396
import Proofs.RadenkovicGutmanD1Long00Leaf01397
import Proofs.RadenkovicGutmanD1Long00Leaf01398
import Proofs.RadenkovicGutmanD1Long00Leaf01399
import Proofs.RadenkovicGutmanD1Long00Leaf01400CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01401CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01402CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01403CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01404CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01405CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01406CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01407CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01408CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01409CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01410
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0082Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01394) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01395) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01396) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01397) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01398) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01399) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01400) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01401) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01402) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01403) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01404) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01405) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01406) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01407) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01408) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01409) (.leaf DegreeOneLongClass00.leaf01410))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/19),(32/9),(106993167/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/19) (32/9) 0 1 0 1 (106993167/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01394_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01395_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01396_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01397_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01398_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01399_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01400_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01401_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01402_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01403_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01404_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01405_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01406_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01407_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01408_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01409_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01410_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/9) : ℚ) : ℝ)-(((64/19) : ℚ) : ℝ))*(((106993167/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/19) : ℚ) : ℝ)..(((32/9) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0082Complete
