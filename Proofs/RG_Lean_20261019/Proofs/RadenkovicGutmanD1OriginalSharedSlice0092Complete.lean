/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01564
import Proofs.RadenkovicGutmanD1Long00Leaf01565
import Proofs.RadenkovicGutmanD1Long00Leaf01566
import Proofs.RadenkovicGutmanD1Long00Leaf01567
import Proofs.RadenkovicGutmanD1Long00Leaf01568
import Proofs.RadenkovicGutmanD1Long00Leaf01569
import Proofs.RadenkovicGutmanD1Long00Leaf01570
import Proofs.RadenkovicGutmanD1Long00Leaf01571
import Proofs.RadenkovicGutmanD1Long00Leaf01572
import Proofs.RadenkovicGutmanD1Long00Leaf01573
import Proofs.RadenkovicGutmanD1Long00Leaf01574
import Proofs.RadenkovicGutmanD1Long00Leaf01575
import Proofs.RadenkovicGutmanD1Long00Leaf01576
import Proofs.RadenkovicGutmanD1Long00Leaf01577
import Proofs.RadenkovicGutmanD1Long00Leaf01578
import Proofs.RadenkovicGutmanD1Long00Leaf01579
import Proofs.RadenkovicGutmanD1Long00Leaf01580
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0092Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01564) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01565) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01566) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01567) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01568) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01569) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01570) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01571) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01572) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01573) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01574) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01575) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01576) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01577) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01578) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01579) (.leaf DegreeOneLongClass00.leaf01580))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/19),(64/9),(72442263/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (128/19) (64/9) 0 1 0 1 (72442263/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01564_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01565_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01566_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01567_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01568_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01569_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01570_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01571_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01572_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01573_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01574_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01575_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01576_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01577_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01578_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01579_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01580_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/9) : ℚ) : ℝ)-(((128/19) : ℚ) : ℝ))*(((72442263/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((128/19) : ℚ) : ℝ)..(((64/9) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0092Complete
