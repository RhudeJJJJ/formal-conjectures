/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00068
import Proofs.RadenkovicGutmanD1Long00Leaf00069
import Proofs.RadenkovicGutmanD1Long00Leaf00070
import Proofs.RadenkovicGutmanD1Long00Leaf00071
import Proofs.RadenkovicGutmanD1Long00Leaf00072
import Proofs.RadenkovicGutmanD1Long00Leaf00073
import Proofs.RadenkovicGutmanD1Long00Leaf00074
import Proofs.RadenkovicGutmanD1Long00Leaf00075
import Proofs.RadenkovicGutmanD1Long00Leaf00076
import Proofs.RadenkovicGutmanD1Long00Leaf00077
import Proofs.RadenkovicGutmanD1Long00Leaf00078
import Proofs.RadenkovicGutmanD1Long00Leaf00079
import Proofs.RadenkovicGutmanD1Long00Leaf00080
import Proofs.RadenkovicGutmanD1Long00Leaf00081
import Proofs.RadenkovicGutmanD1Long00Leaf00082
import Proofs.RadenkovicGutmanD1Long00Leaf00083
import Proofs.RadenkovicGutmanD1Long00Leaf00084
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0004Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00068) (.leaf DegreeOneLongClass00.leaf00069)) (.leaf DegreeOneLongClass00.leaf00070)) (.leaf DegreeOneLongClass00.leaf00071)) (.leaf DegreeOneLongClass00.leaf00072)) (.leaf DegreeOneLongClass00.leaf00073)) (.leaf DegreeOneLongClass00.leaf00074)) (.leaf DegreeOneLongClass00.leaf00075)) (.leaf DegreeOneLongClass00.leaf00076)) (.leaf DegreeOneLongClass00.leaf00077)) (.leaf DegreeOneLongClass00.leaf00078)) (.leaf DegreeOneLongClass00.leaf00079)) (.leaf DegreeOneLongClass00.leaf00080)) (.leaf DegreeOneLongClass00.leaf00081)) (.leaf DegreeOneLongClass00.leaf00082)) (.leaf DegreeOneLongClass00.leaf00083)) (.leaf DegreeOneLongClass00.leaf00084)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/4000),(1/500),(-5093764077/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/4000) (1/500) 0 1 0 1 (-5093764077/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00068_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00069_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00070_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00071_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00072_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00073_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00074_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00075_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00076_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00077_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00078_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00079_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00080_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00081_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00082_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00083_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00084_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/500) : ℚ) : ℝ)-(((7/4000) : ℚ) : ℝ))*(((-5093764077/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/4000) : ℚ) : ℝ)..(((1/500) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0004Complete
