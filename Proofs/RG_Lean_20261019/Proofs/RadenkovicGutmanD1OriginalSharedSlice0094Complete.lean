/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01598CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01599CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01600CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01601CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01602CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01603CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01604CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01605CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01606CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01607CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01608CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01609CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01610CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01613CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01614CompositionalRepair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0094Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01598) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01599) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01600) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01601) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01602) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01603) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01604) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01605) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01606) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01607) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01608) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01609) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01610) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01611) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01612) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01613) (.leaf DegreeOneLongClass00.leaf01614))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/17),8,(58737041/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (128/17) 8 0 1 0 1 (58737041/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01598_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01599_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01600_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01601_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01602_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01603_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01604_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01605_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01606_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01607_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01608_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01609_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01610_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01611_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01612_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01613_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01614_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    (((8 : ℚ) : ℝ)-(((128/17) : ℚ) : ℝ))*(((58737041/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((128/17) : ℚ) : ℝ)..((8 : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0094Complete
