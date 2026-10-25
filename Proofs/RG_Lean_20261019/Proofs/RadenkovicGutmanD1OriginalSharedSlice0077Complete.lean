/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01309Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01310
import Proofs.RadenkovicGutmanD1Long00Leaf01311
import Proofs.RadenkovicGutmanD1Long00Leaf01312
import Proofs.RadenkovicGutmanD1Long00Leaf01313
import Proofs.RadenkovicGutmanD1Long00Leaf01314
import Proofs.RadenkovicGutmanD1Long00Leaf01315
import Proofs.RadenkovicGutmanD1Long00Leaf01316
import Proofs.RadenkovicGutmanD1Long00Leaf01317
import Proofs.RadenkovicGutmanD1Long00Leaf01318
import Proofs.RadenkovicGutmanD1Long00Leaf01319
import Proofs.RadenkovicGutmanD1Long00Leaf01320
import Proofs.RadenkovicGutmanD1Long00Leaf01321
import Proofs.RadenkovicGutmanD1Long00Leaf01322
import Proofs.RadenkovicGutmanD1Long00Leaf01323
import Proofs.RadenkovicGutmanD1Long00Leaf01324
import Proofs.RadenkovicGutmanD1Long00Leaf01325
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0077Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01309) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01310) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01311) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01312) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01313) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01314) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01315) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01316) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01317) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01318) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01319) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01320) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01321) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01322) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01323) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01324) (.leaf DegreeOneLongClass00.leaf01325))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(16/7),(32/13),(79516117/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (16/7) (32/13) 0 1 0 1 (79516117/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01309_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01310_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01311_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01312_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01313_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01314_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01315_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01316_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01317_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01318_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01319_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01320_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01321_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01322_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01323_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01324_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01325_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/13) : ℚ) : ℝ)-(((16/7) : ℚ) : ℝ))*(((79516117/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((16/7) : ℚ) : ℝ)..(((32/13) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0077Complete
