/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00493
import Proofs.RadenkovicGutmanD1Long00Leaf00494
import Proofs.RadenkovicGutmanD1Long00Leaf00495
import Proofs.RadenkovicGutmanD1Long00Leaf00496
import Proofs.RadenkovicGutmanD1Long00Leaf00497
import Proofs.RadenkovicGutmanD1Long00Leaf00498
import Proofs.RadenkovicGutmanD1Long00Leaf00499
import Proofs.RadenkovicGutmanD1Long00Leaf00500
import Proofs.RadenkovicGutmanD1Long00Leaf00501
import Proofs.RadenkovicGutmanD1Long00Leaf00502
import Proofs.RadenkovicGutmanD1Long00Leaf00503
import Proofs.RadenkovicGutmanD1Long00Leaf00504
import Proofs.RadenkovicGutmanD1Long00Leaf00505
import Proofs.RadenkovicGutmanD1Long00Leaf00506
import Proofs.RadenkovicGutmanD1Long00Leaf00507
import Proofs.RadenkovicGutmanD1Long00Leaf00508
import Proofs.RadenkovicGutmanD1Long00Leaf00509
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0029Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00493) (.leaf DegreeOneLongClass00.leaf00494)) (.leaf DegreeOneLongClass00.leaf00495)) (.leaf DegreeOneLongClass00.leaf00496)) (.leaf DegreeOneLongClass00.leaf00497)) (.leaf DegreeOneLongClass00.leaf00498)) (.leaf DegreeOneLongClass00.leaf00499)) (.leaf DegreeOneLongClass00.leaf00500)) (.leaf DegreeOneLongClass00.leaf00501)) (.leaf DegreeOneLongClass00.leaf00502)) (.leaf DegreeOneLongClass00.leaf00503)) (.leaf DegreeOneLongClass00.leaf00504)) (.leaf DegreeOneLongClass00.leaf00505)) (.leaf DegreeOneLongClass00.leaf00506)) (.leaf DegreeOneLongClass00.leaf00507)) (.leaf DegreeOneLongClass00.leaf00508)) (.leaf DegreeOneLongClass00.leaf00509)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(13/800),(7/400),(-10798016813/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (13/800) (7/400) 0 1 0 1 (-10798016813/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00493_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00494_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00495_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00496_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00497_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00498_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00499_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00500_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00501_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00502_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00503_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00504_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00505_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00506_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00507_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00508_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00509_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/400) : ℚ) : ℝ)-(((13/800) : ℚ) : ℝ))*(((-10798016813/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((13/800) : ℚ) : ℝ)..(((7/400) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0029Complete
