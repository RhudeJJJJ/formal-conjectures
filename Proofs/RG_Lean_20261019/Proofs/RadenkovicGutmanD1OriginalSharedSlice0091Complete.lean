/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01547
import Proofs.RadenkovicGutmanD1Long00Leaf01548
import Proofs.RadenkovicGutmanD1Long00Leaf01549
import Proofs.RadenkovicGutmanD1Long00Leaf01550
import Proofs.RadenkovicGutmanD1Long00Leaf01551
import Proofs.RadenkovicGutmanD1Long00Leaf01552
import Proofs.RadenkovicGutmanD1Long00Leaf01553
import Proofs.RadenkovicGutmanD1Long00Leaf01554
import Proofs.RadenkovicGutmanD1Long00Leaf01555
import Proofs.RadenkovicGutmanD1Long00Leaf01556
import Proofs.RadenkovicGutmanD1Long00Leaf01557
import Proofs.RadenkovicGutmanD1Long00Leaf01558
import Proofs.RadenkovicGutmanD1Long00Leaf01559
import Proofs.RadenkovicGutmanD1Long00Leaf01560
import Proofs.RadenkovicGutmanD1Long00Leaf01561
import Proofs.RadenkovicGutmanD1Long00Leaf01562
import Proofs.RadenkovicGutmanD1Long00Leaf01563
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0091Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01547) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01548) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01549) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01550) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01551) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01552) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01553) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01554) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01555) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01556) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01557) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01558) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01559) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01560) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01561) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01562) (.leaf DegreeOneLongClass00.leaf01563))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/5),(128/19),(19905963/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/5) (128/19) 0 1 0 1 (19905963/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01547_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01548_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01549_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01550_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01551_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01552_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01553_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01554_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01555_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01556_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01557_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01558_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01559_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01560_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01561_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01562_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01563_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/19) : ℚ) : ℝ)-(((32/5) : ℚ) : ℝ))*(((19905963/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/5) : ℚ) : ℝ)..(((128/19) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0091Complete
