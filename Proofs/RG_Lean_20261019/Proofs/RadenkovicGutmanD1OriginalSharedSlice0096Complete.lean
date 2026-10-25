/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01632
import Proofs.RadenkovicGutmanD1Long00Leaf01633
import Proofs.RadenkovicGutmanD1Long00Leaf01634
import Proofs.RadenkovicGutmanD1Long00Leaf01635
import Proofs.RadenkovicGutmanD1Long00Leaf01636
import Proofs.RadenkovicGutmanD1Long00Leaf01637
import Proofs.RadenkovicGutmanD1Long00Leaf01638
import Proofs.RadenkovicGutmanD1Long00Leaf01639
import Proofs.RadenkovicGutmanD1Long00Leaf01640
import Proofs.RadenkovicGutmanD1Long00Leaf01641
import Proofs.RadenkovicGutmanD1Long00Leaf01642
import Proofs.RadenkovicGutmanD1Long00Leaf01643
import Proofs.RadenkovicGutmanD1Long00Leaf01644
import Proofs.RadenkovicGutmanD1Long00Leaf01645
import Proofs.RadenkovicGutmanD1Long00Leaf01646
import Proofs.RadenkovicGutmanD1Long00Leaf01647
import Proofs.RadenkovicGutmanD1Long00Leaf01648
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0096Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01632) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01633) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01634) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01635) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01636) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01637) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01638) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01639) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01640) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01641) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01642) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01643) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01644) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01645) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01646) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01647) (.leaf DegreeOneLongClass00.leaf01648))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/15),(64/7),(2878757/268435456)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (128/15) (64/7) 0 1 0 1 (2878757/268435456) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01632_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01633_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01634_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01635_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01636_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01637_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01638_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01639_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01640_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01641_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01642_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01643_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01644_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01645_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01646_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01647_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01648_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/7) : ℚ) : ℝ)-(((128/15) : ℚ) : ℝ))*(((2878757/268435456) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((128/15) : ℚ) : ℝ)..(((64/7) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0096Complete
