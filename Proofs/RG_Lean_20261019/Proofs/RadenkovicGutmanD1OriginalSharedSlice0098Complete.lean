/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01666
import Proofs.RadenkovicGutmanD1Long00Leaf01667
import Proofs.RadenkovicGutmanD1Long00Leaf01668
import Proofs.RadenkovicGutmanD1Long00Leaf01669
import Proofs.RadenkovicGutmanD1Long00Leaf01670CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01671CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01672CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01673CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01674CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01675CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01676CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01677CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01678CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01679CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01680
import Proofs.RadenkovicGutmanD1Long00Leaf01681
import Proofs.RadenkovicGutmanD1Long00Leaf01682
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0098Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01666) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01667) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01668) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01669) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01670) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01671) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01672) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01673) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01674) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01675) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01676) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01677) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01678) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01679) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01680) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01681) (.leaf DegreeOneLongClass00.leaf01682))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/13),(32/3),(34590987/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (128/13) (32/3) 0 1 0 1 (34590987/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01666_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01667_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01668_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01669_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01670_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01671_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01672_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01673_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01674_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01675_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01676_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01677_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01678_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01679_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01680_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01681_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01682_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/3) : ℚ) : ℝ)-(((128/13) : ℚ) : ℝ))*(((34590987/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((128/13) : ℚ) : ℝ)..(((32/3) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0098Complete
