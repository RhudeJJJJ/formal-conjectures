/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01615CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01616CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01617CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01618CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01619CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01620
import Proofs.RadenkovicGutmanD1Long00Leaf01621
import Proofs.RadenkovicGutmanD1Long00Leaf01622
import Proofs.RadenkovicGutmanD1Long00Leaf01623
import Proofs.RadenkovicGutmanD1Long00Leaf01624
import Proofs.RadenkovicGutmanD1Long00Leaf01625
import Proofs.RadenkovicGutmanD1Long00Leaf01626
import Proofs.RadenkovicGutmanD1Long00Leaf01627
import Proofs.RadenkovicGutmanD1Long00Leaf01628
import Proofs.RadenkovicGutmanD1Long00Leaf01629
import Proofs.RadenkovicGutmanD1Long00Leaf01630
import Proofs.RadenkovicGutmanD1Long00Leaf01631
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0095Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01615) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01616) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01617) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01618) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01619) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01620) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01621) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01622) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01623) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01624) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01625) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01626) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01627) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01628) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01629) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01630) (.leaf DegreeOneLongClass00.leaf01631))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,8,(128/15),(52258739/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 8 (128/15) 0 1 0 1 (52258739/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01615_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01616_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01617_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01618_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01619_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01620_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01621_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01622_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01623_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01624_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01625_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01626_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01627_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01628_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01629_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01630_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01631_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/15) : ℚ) : ℝ)-((8 : ℚ) : ℝ))*(((52258739/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in ((8 : ℚ) : ℝ)..(((128/15) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0095Complete
