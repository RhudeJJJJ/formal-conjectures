/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00833
import Proofs.RadenkovicGutmanD1Long00Leaf00834
import Proofs.RadenkovicGutmanD1Long00Leaf00835
import Proofs.RadenkovicGutmanD1Long00Leaf00836
import Proofs.RadenkovicGutmanD1Long00Leaf00837
import Proofs.RadenkovicGutmanD1Long00Leaf00838
import Proofs.RadenkovicGutmanD1Long00Leaf00839
import Proofs.RadenkovicGutmanD1Long00Leaf00840
import Proofs.RadenkovicGutmanD1Long00Leaf00841
import Proofs.RadenkovicGutmanD1Long00Leaf00842
import Proofs.RadenkovicGutmanD1Long00Leaf00843
import Proofs.RadenkovicGutmanD1Long00Leaf00844
import Proofs.RadenkovicGutmanD1Long00Leaf00845
import Proofs.RadenkovicGutmanD1Long00Leaf00846
import Proofs.RadenkovicGutmanD1Long00Leaf00847
import Proofs.RadenkovicGutmanD1Long00Leaf00848
import Proofs.RadenkovicGutmanD1Long00Leaf00849
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0049Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00833) (.leaf DegreeOneLongClass00.leaf00834)) (.leaf DegreeOneLongClass00.leaf00835)) (.leaf DegreeOneLongClass00.leaf00836)) (.leaf DegreeOneLongClass00.leaf00837)) (.leaf DegreeOneLongClass00.leaf00838)) (.leaf DegreeOneLongClass00.leaf00839)) (.leaf DegreeOneLongClass00.leaf00840)) (.leaf DegreeOneLongClass00.leaf00841)) (.leaf DegreeOneLongClass00.leaf00842)) (.leaf DegreeOneLongClass00.leaf00843)) (.leaf DegreeOneLongClass00.leaf00844)) (.leaf DegreeOneLongClass00.leaf00845)) (.leaf DegreeOneLongClass00.leaf00846)) (.leaf DegreeOneLongClass00.leaf00847)) (.leaf DegreeOneLongClass00.leaf00848)) (.leaf DegreeOneLongClass00.leaf00849)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/20),(13/80),(-1131452621/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/20) (13/80) 0 1 0 1 (-1131452621/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00833_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00834_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00835_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00836_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00837_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00838_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00839_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00840_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00841_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00842_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00843_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00844_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00845_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00846_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00847_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00848_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00849_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((13/80) : ℚ) : ℝ)-(((3/20) : ℚ) : ℝ))*(((-1131452621/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/20) : ℚ) : ℝ)..(((13/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0049Complete
