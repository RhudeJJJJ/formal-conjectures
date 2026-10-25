/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00476
import Proofs.RadenkovicGutmanD1Long00Leaf00477
import Proofs.RadenkovicGutmanD1Long00Leaf00478
import Proofs.RadenkovicGutmanD1Long00Leaf00479
import Proofs.RadenkovicGutmanD1Long00Leaf00480
import Proofs.RadenkovicGutmanD1Long00Leaf00481
import Proofs.RadenkovicGutmanD1Long00Leaf00482
import Proofs.RadenkovicGutmanD1Long00Leaf00483
import Proofs.RadenkovicGutmanD1Long00Leaf00484
import Proofs.RadenkovicGutmanD1Long00Leaf00485
import Proofs.RadenkovicGutmanD1Long00Leaf00486
import Proofs.RadenkovicGutmanD1Long00Leaf00487
import Proofs.RadenkovicGutmanD1Long00Leaf00488
import Proofs.RadenkovicGutmanD1Long00Leaf00489
import Proofs.RadenkovicGutmanD1Long00Leaf00490
import Proofs.RadenkovicGutmanD1Long00Leaf00491
import Proofs.RadenkovicGutmanD1Long00Leaf00492
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0028Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00476) (.leaf DegreeOneLongClass00.leaf00477)) (.leaf DegreeOneLongClass00.leaf00478)) (.leaf DegreeOneLongClass00.leaf00479)) (.leaf DegreeOneLongClass00.leaf00480)) (.leaf DegreeOneLongClass00.leaf00481)) (.leaf DegreeOneLongClass00.leaf00482)) (.leaf DegreeOneLongClass00.leaf00483)) (.leaf DegreeOneLongClass00.leaf00484)) (.leaf DegreeOneLongClass00.leaf00485)) (.leaf DegreeOneLongClass00.leaf00486)) (.leaf DegreeOneLongClass00.leaf00487)) (.leaf DegreeOneLongClass00.leaf00488)) (.leaf DegreeOneLongClass00.leaf00489)) (.leaf DegreeOneLongClass00.leaf00490)) (.leaf DegreeOneLongClass00.leaf00491)) (.leaf DegreeOneLongClass00.leaf00492)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/200),(13/800),(-11139361995/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/200) (13/800) 0 1 0 1 (-11139361995/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00476_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00477_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00478_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00479_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00480_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00481_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00482_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00483_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00484_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00485_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00486_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00487_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00488_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00489_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00490_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00491_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00492_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((13/800) : ℚ) : ℝ)-(((3/200) : ℚ) : ℝ))*(((-11139361995/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/200) : ℚ) : ℝ)..(((13/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0028Complete
