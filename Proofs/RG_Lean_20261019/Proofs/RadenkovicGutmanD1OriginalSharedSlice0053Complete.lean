/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00901
import Proofs.RadenkovicGutmanD1Long00Leaf00902
import Proofs.RadenkovicGutmanD1Long00Leaf00903
import Proofs.RadenkovicGutmanD1Long00Leaf00904
import Proofs.RadenkovicGutmanD1Long00Leaf00905
import Proofs.RadenkovicGutmanD1Long00Leaf00906
import Proofs.RadenkovicGutmanD1Long00Leaf00907
import Proofs.RadenkovicGutmanD1Long00Leaf00908
import Proofs.RadenkovicGutmanD1Long00Leaf00909
import Proofs.RadenkovicGutmanD1Long00Leaf00910
import Proofs.RadenkovicGutmanD1Long00Leaf00911
import Proofs.RadenkovicGutmanD1Long00Leaf00912
import Proofs.RadenkovicGutmanD1Long00Leaf00913
import Proofs.RadenkovicGutmanD1Long00Leaf00914
import Proofs.RadenkovicGutmanD1Long00Leaf00915
import Proofs.RadenkovicGutmanD1Long00Leaf00916
import Proofs.RadenkovicGutmanD1Long00Leaf00917
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0053Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00901) (.leaf DegreeOneLongClass00.leaf00902)) (.leaf DegreeOneLongClass00.leaf00903)) (.leaf DegreeOneLongClass00.leaf00904)) (.leaf DegreeOneLongClass00.leaf00905)) (.leaf DegreeOneLongClass00.leaf00906)) (.leaf DegreeOneLongClass00.leaf00907)) (.leaf DegreeOneLongClass00.leaf00908)) (.leaf DegreeOneLongClass00.leaf00909)) (.leaf DegreeOneLongClass00.leaf00910)) (.leaf DegreeOneLongClass00.leaf00911)) (.leaf DegreeOneLongClass00.leaf00912)) (.leaf DegreeOneLongClass00.leaf00913)) (.leaf DegreeOneLongClass00.leaf00914)) (.leaf DegreeOneLongClass00.leaf00915)) (.leaf DegreeOneLongClass00.leaf00916)) (.leaf DegreeOneLongClass00.leaf00917)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/32),(19/80),(-1354109189/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/32) (19/80) 0 1 0 1 (-1354109189/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00901_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00902_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00903_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00904_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00905_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00906_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00907_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00908_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00909_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00910_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00911_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00912_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00913_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00914_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00915_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00916_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00917_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((19/80) : ℚ) : ℝ)-(((7/32) : ℚ) : ℝ))*(((-1354109189/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/32) : ℚ) : ℝ)..(((19/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0053Complete
