/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01343CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01344CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01345CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01346CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01347CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01348CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01349CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01350
import Proofs.RadenkovicGutmanD1Long00Leaf01351
import Proofs.RadenkovicGutmanD1Long00Leaf01352
import Proofs.RadenkovicGutmanD1Long00Leaf01353
import Proofs.RadenkovicGutmanD1Long00Leaf01354
import Proofs.RadenkovicGutmanD1Long00Leaf01355
import Proofs.RadenkovicGutmanD1Long00Leaf01356
import Proofs.RadenkovicGutmanD1Long00Leaf01357
import Proofs.RadenkovicGutmanD1Long00Leaf01358
import Proofs.RadenkovicGutmanD1Long00Leaf01359
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0079Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01343) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01344) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01345) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01346) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01347) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01348) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01349) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01350) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01351) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01352) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01353) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01354) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01355) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01356) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01357) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01358) (.leaf DegreeOneLongClass00.leaf01359))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(8/3),(32/11),(271125169/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (8/3) (32/11) 0 1 0 1 (271125169/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01343_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01344_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01345_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01346_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01347_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01348_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01349_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01350_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01351_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01352_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01353_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01354_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01355_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01356_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01357_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01358_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01359_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/11) : ℚ) : ℝ)-(((8/3) : ℚ) : ℝ))*(((271125169/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((8/3) : ℚ) : ℝ)..(((32/11) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0079Complete
