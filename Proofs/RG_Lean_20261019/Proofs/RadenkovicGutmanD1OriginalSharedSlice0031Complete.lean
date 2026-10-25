/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00527
import Proofs.RadenkovicGutmanD1Long00Leaf00528
import Proofs.RadenkovicGutmanD1Long00Leaf00529
import Proofs.RadenkovicGutmanD1Long00Leaf00530
import Proofs.RadenkovicGutmanD1Long00Leaf00531
import Proofs.RadenkovicGutmanD1Long00Leaf00532
import Proofs.RadenkovicGutmanD1Long00Leaf00533
import Proofs.RadenkovicGutmanD1Long00Leaf00534
import Proofs.RadenkovicGutmanD1Long00Leaf00535
import Proofs.RadenkovicGutmanD1Long00Leaf00536
import Proofs.RadenkovicGutmanD1Long00Leaf00537
import Proofs.RadenkovicGutmanD1Long00Leaf00538
import Proofs.RadenkovicGutmanD1Long00Leaf00539
import Proofs.RadenkovicGutmanD1Long00Leaf00540
import Proofs.RadenkovicGutmanD1Long00Leaf00541
import Proofs.RadenkovicGutmanD1Long00Leaf00542
import Proofs.RadenkovicGutmanD1Long00Leaf00543
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0031Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00527) (.leaf DegreeOneLongClass00.leaf00528)) (.leaf DegreeOneLongClass00.leaf00529)) (.leaf DegreeOneLongClass00.leaf00530)) (.leaf DegreeOneLongClass00.leaf00531)) (.leaf DegreeOneLongClass00.leaf00532)) (.leaf DegreeOneLongClass00.leaf00533)) (.leaf DegreeOneLongClass00.leaf00534)) (.leaf DegreeOneLongClass00.leaf00535)) (.leaf DegreeOneLongClass00.leaf00536)) (.leaf DegreeOneLongClass00.leaf00537)) (.leaf DegreeOneLongClass00.leaf00538)) (.leaf DegreeOneLongClass00.leaf00539)) (.leaf DegreeOneLongClass00.leaf00540)) (.leaf DegreeOneLongClass00.leaf00541)) (.leaf DegreeOneLongClass00.leaf00542)) (.leaf DegreeOneLongClass00.leaf00543)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/50),(7/320),(-9914674625/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/50) (7/320) 0 1 0 1 (-9914674625/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00527_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00528_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00529_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00530_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00531_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00532_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00533_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00534_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00535_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00536_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00537_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00538_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00539_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00540_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00541_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00542_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00543_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/320) : ℚ) : ℝ)-(((1/50) : ℚ) : ℝ))*(((-9914674625/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/50) : ℚ) : ℝ)..(((7/320) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0031Complete
