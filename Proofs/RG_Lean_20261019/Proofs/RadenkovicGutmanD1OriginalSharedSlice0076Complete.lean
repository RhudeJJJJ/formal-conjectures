/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01292Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01293Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01294Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01295Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01296Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01297Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01298Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01299Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01300Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01301Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01302Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01303Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01304Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01305Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01306Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01307Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01308Repair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0076Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01292) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01293) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01294) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01295) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01296) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01297) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01298) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01299) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01300) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01301) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01302) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01303) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01304) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01305) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01306) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01307) (.leaf DegreeOneLongClass00.leaf01308))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/15),(16/7),(337090277/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/15) (16/7) 0 1 0 1 (337090277/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01292_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01293_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01294_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01295_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01296_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01297_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01298_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01299_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01300_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01301_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01302_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01303_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01304_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01305_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01306_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01307_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01308_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((16/7) : ℚ) : ℝ)-(((32/15) : ℚ) : ℝ))*(((337090277/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/15) : ℚ) : ℝ)..(((16/7) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0076Complete
