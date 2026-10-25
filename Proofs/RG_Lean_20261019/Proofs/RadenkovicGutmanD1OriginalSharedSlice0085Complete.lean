/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01445CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01446CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01447CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01448CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01449CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01450
import Proofs.RadenkovicGutmanD1Long00Leaf01451
import Proofs.RadenkovicGutmanD1Long00Leaf01452
import Proofs.RadenkovicGutmanD1Long00Leaf01453
import Proofs.RadenkovicGutmanD1Long00Leaf01454
import Proofs.RadenkovicGutmanD1Long00Leaf01455
import Proofs.RadenkovicGutmanD1Long00Leaf01456
import Proofs.RadenkovicGutmanD1Long00Leaf01457
import Proofs.RadenkovicGutmanD1Long00Leaf01458
import Proofs.RadenkovicGutmanD1Long00Leaf01459
import Proofs.RadenkovicGutmanD1Long00Leaf01460
import Proofs.RadenkovicGutmanD1Long00Leaf01461
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0085Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01445) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01446) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01447) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01448) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01449) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01450) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01451) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01452) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01453) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01454) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01455) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01456) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01457) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01458) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01459) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01460) (.leaf DegreeOneLongClass00.leaf01461))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,4,(64/15),(166363123/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 4 (64/15) 0 1 0 1 (166363123/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01445_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01446_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01447_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01448_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01449_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01450_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01451_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01452_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01453_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01454_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01455_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01456_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01457_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01458_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01459_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01460_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01461_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/15) : ℚ) : ℝ)-((4 : ℚ) : ℝ))*(((166363123/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in ((4 : ℚ) : ℝ)..(((64/15) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0085Complete
