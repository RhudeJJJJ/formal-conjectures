/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00697
import Proofs.RadenkovicGutmanD1Long00Leaf00698
import Proofs.RadenkovicGutmanD1Long00Leaf00699
import Proofs.RadenkovicGutmanD1Long00Leaf00700
import Proofs.RadenkovicGutmanD1Long00Leaf00701
import Proofs.RadenkovicGutmanD1Long00Leaf00702
import Proofs.RadenkovicGutmanD1Long00Leaf00703
import Proofs.RadenkovicGutmanD1Long00Leaf00704
import Proofs.RadenkovicGutmanD1Long00Leaf00705
import Proofs.RadenkovicGutmanD1Long00Leaf00706
import Proofs.RadenkovicGutmanD1Long00Leaf00707
import Proofs.RadenkovicGutmanD1Long00Leaf00708
import Proofs.RadenkovicGutmanD1Long00Leaf00709
import Proofs.RadenkovicGutmanD1Long00Leaf00710
import Proofs.RadenkovicGutmanD1Long00Leaf00711
import Proofs.RadenkovicGutmanD1Long00Leaf00712
import Proofs.RadenkovicGutmanD1Long00Leaf00713
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0041Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00697) (.leaf DegreeOneLongClass00.leaf00698)) (.leaf DegreeOneLongClass00.leaf00699)) (.leaf DegreeOneLongClass00.leaf00700)) (.leaf DegreeOneLongClass00.leaf00701)) (.leaf DegreeOneLongClass00.leaf00702)) (.leaf DegreeOneLongClass00.leaf00703)) (.leaf DegreeOneLongClass00.leaf00704)) (.leaf DegreeOneLongClass00.leaf00705)) (.leaf DegreeOneLongClass00.leaf00706)) (.leaf DegreeOneLongClass00.leaf00707)) (.leaf DegreeOneLongClass00.leaf00708)) (.leaf DegreeOneLongClass00.leaf00709)) (.leaf DegreeOneLongClass00.leaf00710)) (.leaf DegreeOneLongClass00.leaf00711)) (.leaf DegreeOneLongClass00.leaf00712)) (.leaf DegreeOneLongClass00.leaf00713)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/16),(11/160),(-5225272661/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/16) (11/160) 0 1 0 1 (-5225272661/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00697_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00698_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00699_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00700_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00701_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00702_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00703_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00704_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00705_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00706_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00707_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00708_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00709_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00710_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00711_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00712_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00713_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/160) : ℚ) : ℝ)-(((1/16) : ℚ) : ℝ))*(((-5225272661/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/16) : ℚ) : ℝ)..(((11/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0041Complete
