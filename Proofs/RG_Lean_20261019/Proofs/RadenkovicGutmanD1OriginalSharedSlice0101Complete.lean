/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01717
import Proofs.RadenkovicGutmanD1Long00Leaf01718
import Proofs.RadenkovicGutmanD1Long00Leaf01719
import Proofs.RadenkovicGutmanD1Long00Leaf01720
import Proofs.RadenkovicGutmanD1Long00Leaf01721
import Proofs.RadenkovicGutmanD1Long00Leaf01722
import Proofs.RadenkovicGutmanD1Long00Leaf01723
import Proofs.RadenkovicGutmanD1Long00Leaf01724
import Proofs.RadenkovicGutmanD1Long00Leaf01725
import Proofs.RadenkovicGutmanD1Long00Leaf01726
import Proofs.RadenkovicGutmanD1Long00Leaf01727
import Proofs.RadenkovicGutmanD1Long00Leaf01728
import Proofs.RadenkovicGutmanD1Long00Leaf01729
import Proofs.RadenkovicGutmanD1Long00Leaf01730
import Proofs.RadenkovicGutmanD1Long00Leaf01731
import Proofs.RadenkovicGutmanD1Long00Leaf01732
import Proofs.RadenkovicGutmanD1Long00Leaf01733
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0101Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01717) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01718) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01719) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01720) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01721) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01722) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01723) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01724) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01725) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01726) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01727) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01728) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01729) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01730) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01731) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01732) (.leaf DegreeOneLongClass00.leaf01733))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/5),(128/9),(5007541/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/5) (128/9) 0 1 0 1 (5007541/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01717_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01718_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01719_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01720_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01721_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01722_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01723_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01724_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01725_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01726_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01727_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01728_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01729_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01730_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01731_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01732_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01733_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/9) : ℚ) : ℝ)-(((64/5) : ℚ) : ℝ))*(((5007541/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/5) : ℚ) : ℝ)..(((128/9) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0101Complete
