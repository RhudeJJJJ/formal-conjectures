/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01513Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01514Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01515Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01516CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01517CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01518CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01519CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01520
import Proofs.RadenkovicGutmanD1Long00Leaf01521
import Proofs.RadenkovicGutmanD1Long00Leaf01522
import Proofs.RadenkovicGutmanD1Long00Leaf01523
import Proofs.RadenkovicGutmanD1Long00Leaf01524
import Proofs.RadenkovicGutmanD1Long00Leaf01525
import Proofs.RadenkovicGutmanD1Long00Leaf01526
import Proofs.RadenkovicGutmanD1Long00Leaf01527
import Proofs.RadenkovicGutmanD1Long00Leaf01528
import Proofs.RadenkovicGutmanD1Long00Leaf01529
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0089Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01513) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01514) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01515) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01516) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01517) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01518) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01519) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01520) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01521) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01522) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01523) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01524) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01525) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01526) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01527) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01528) (.leaf DegreeOneLongClass00.leaf01529))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(16/3),(64/11),(102159797/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (16/3) (64/11) 0 1 0 1 (102159797/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01513_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01514_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01515_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01516_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01517_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01518_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01519_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01520_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01521_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01522_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01523_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01524_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01525_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01526_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01527_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01528_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01529_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/11) : ℚ) : ℝ)-(((16/3) : ℚ) : ℝ))*(((102159797/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((16/3) : ℚ) : ℝ)..(((64/11) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0089Complete
