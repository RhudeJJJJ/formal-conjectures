/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01496CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01497CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01498CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01499CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01500CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01501CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01502CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01503CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01504CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01505CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01506CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01507CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01508CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01509CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01510CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01511CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01512CompositionalRepair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0088Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01496) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01497) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01498) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01499) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01500) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01501) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01502) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01503) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01504) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01505) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01506) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01507) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01508) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01509) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01510) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01511) (.leaf DegreeOneLongClass00.leaf01512))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/13),(16/3),(29467937/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/13) (16/3) 0 1 0 1 (29467937/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01496_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01497_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01498_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01499_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01500_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01501_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01502_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01503_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01504_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01505_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01506_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01507_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01508_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01509_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01510_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01511_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01512_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((16/3) : ℚ) : ℝ)-(((64/13) : ℚ) : ℝ))*(((29467937/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/13) : ℚ) : ℝ)..(((16/3) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0088Complete
