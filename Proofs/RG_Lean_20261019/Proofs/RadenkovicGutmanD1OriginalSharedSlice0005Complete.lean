/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00085
import Proofs.RadenkovicGutmanD1Long00Leaf00086
import Proofs.RadenkovicGutmanD1Long00Leaf00087
import Proofs.RadenkovicGutmanD1Long00Leaf00088
import Proofs.RadenkovicGutmanD1Long00Leaf00089
import Proofs.RadenkovicGutmanD1Long00Leaf00090
import Proofs.RadenkovicGutmanD1Long00Leaf00091
import Proofs.RadenkovicGutmanD1Long00Leaf00092
import Proofs.RadenkovicGutmanD1Long00Leaf00093
import Proofs.RadenkovicGutmanD1Long00Leaf00094
import Proofs.RadenkovicGutmanD1Long00Leaf00095
import Proofs.RadenkovicGutmanD1Long00Leaf00096
import Proofs.RadenkovicGutmanD1Long00Leaf00097
import Proofs.RadenkovicGutmanD1Long00Leaf00098
import Proofs.RadenkovicGutmanD1Long00Leaf00099
import Proofs.RadenkovicGutmanD1Long00Leaf00100
import Proofs.RadenkovicGutmanD1Long00Leaf00101
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0005Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00085) (.leaf DegreeOneLongClass00.leaf00086)) (.leaf DegreeOneLongClass00.leaf00087)) (.leaf DegreeOneLongClass00.leaf00088)) (.leaf DegreeOneLongClass00.leaf00089)) (.leaf DegreeOneLongClass00.leaf00090)) (.leaf DegreeOneLongClass00.leaf00091)) (.leaf DegreeOneLongClass00.leaf00092)) (.leaf DegreeOneLongClass00.leaf00093)) (.leaf DegreeOneLongClass00.leaf00094)) (.leaf DegreeOneLongClass00.leaf00095)) (.leaf DegreeOneLongClass00.leaf00096)) (.leaf DegreeOneLongClass00.leaf00097)) (.leaf DegreeOneLongClass00.leaf00098)) (.leaf DegreeOneLongClass00.leaf00099)) (.leaf DegreeOneLongClass00.leaf00100)) (.leaf DegreeOneLongClass00.leaf00101)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/500),(7/3200),(-9897504295/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/500) (7/3200) 0 1 0 1 (-9897504295/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00085_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00086_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00087_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00088_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00089_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00090_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00091_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00092_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00093_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00094_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00095_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00096_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00097_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00098_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00099_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00100_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00101_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/3200) : ℚ) : ℝ)-(((1/500) : ℚ) : ℝ))*(((-9897504295/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/500) : ℚ) : ℝ)..(((7/3200) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0005Complete
