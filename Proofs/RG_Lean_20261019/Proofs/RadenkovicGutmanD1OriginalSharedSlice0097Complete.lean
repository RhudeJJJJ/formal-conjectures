/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01649
import Proofs.RadenkovicGutmanD1Long00Leaf01650
import Proofs.RadenkovicGutmanD1Long00Leaf01651
import Proofs.RadenkovicGutmanD1Long00Leaf01652
import Proofs.RadenkovicGutmanD1Long00Leaf01653
import Proofs.RadenkovicGutmanD1Long00Leaf01654
import Proofs.RadenkovicGutmanD1Long00Leaf01655
import Proofs.RadenkovicGutmanD1Long00Leaf01656
import Proofs.RadenkovicGutmanD1Long00Leaf01657
import Proofs.RadenkovicGutmanD1Long00Leaf01658
import Proofs.RadenkovicGutmanD1Long00Leaf01659
import Proofs.RadenkovicGutmanD1Long00Leaf01660
import Proofs.RadenkovicGutmanD1Long00Leaf01661
import Proofs.RadenkovicGutmanD1Long00Leaf01662
import Proofs.RadenkovicGutmanD1Long00Leaf01663
import Proofs.RadenkovicGutmanD1Long00Leaf01664
import Proofs.RadenkovicGutmanD1Long00Leaf01665
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0097Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01649) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01650) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01651) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01652) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01653) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01654) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01655) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01656) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01657) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01658) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01659) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01660) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01661) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01662) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01663) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01664) (.leaf DegreeOneLongClass00.leaf01665))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/7),(128/13),(40163521/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/7) (128/13) 0 1 0 1 (40163521/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01649_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01650_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01651_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01652_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01653_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01654_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01655_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01656_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01657_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01658_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01659_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01660_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01661_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01662_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01663_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01664_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01665_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/13) : ℚ) : ℝ)-(((64/7) : ℚ) : ℝ))*(((40163521/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/7) : ℚ) : ℝ)..(((128/13) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0097Complete
