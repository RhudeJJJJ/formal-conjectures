/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01037
import Proofs.RadenkovicGutmanD1Long00Leaf01038
import Proofs.RadenkovicGutmanD1Long00Leaf01039
import Proofs.RadenkovicGutmanD1Long00Leaf01040
import Proofs.RadenkovicGutmanD1Long00Leaf01041
import Proofs.RadenkovicGutmanD1Long00Leaf01042
import Proofs.RadenkovicGutmanD1Long00Leaf01043
import Proofs.RadenkovicGutmanD1Long00Leaf01044
import Proofs.RadenkovicGutmanD1Long00Leaf01045
import Proofs.RadenkovicGutmanD1Long00Leaf01046
import Proofs.RadenkovicGutmanD1Long00Leaf01047
import Proofs.RadenkovicGutmanD1Long00Leaf01048
import Proofs.RadenkovicGutmanD1Long00Leaf01049
import Proofs.RadenkovicGutmanD1Long00Leaf01050
import Proofs.RadenkovicGutmanD1Long00Leaf01051
import Proofs.RadenkovicGutmanD1Long00Leaf01052
import Proofs.RadenkovicGutmanD1Long00Leaf01053
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0061Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.leaf DegreeOneLongClass00.leaf01037) (.leaf DegreeOneLongClass00.leaf01038)) (.first (1/8) (.leaf DegreeOneLongClass00.leaf01039) (.leaf DegreeOneLongClass00.leaf01040))) (.second (1/4) (.first (3/8) (.leaf DegreeOneLongClass00.leaf01041) (.leaf DegreeOneLongClass00.leaf01042)) (.first (3/8) (.leaf DegreeOneLongClass00.leaf01043) (.leaf DegreeOneLongClass00.leaf01044)))) (.first (1/4) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01045) (.leaf DegreeOneLongClass00.leaf01046)) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01047) (.leaf DegreeOneLongClass00.leaf01048)))) (.second (1/2) (.first (3/4) (.second (1/4) (.leaf DegreeOneLongClass00.leaf01049) (.leaf DegreeOneLongClass00.leaf01050)) (.leaf DegreeOneLongClass00.leaf01051)) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01052) (.leaf DegreeOneLongClass00.leaf01053)))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(37/80),(1/2),(-116335685/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (37/80) (1/2) 0 1 0 1 (-116335685/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf01037_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01038_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨DegreeOneLongClass00.leaf01039_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01040_checked,by decide +kernel,by decide +kernel⟩⟩⟩,⟨⟨⟨DegreeOneLongClass00.leaf01041_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01042_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨DegreeOneLongClass00.leaf01043_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01044_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩,⟨⟨⟨DegreeOneLongClass00.leaf01045_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01046_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨DegreeOneLongClass00.leaf01047_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01048_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩,⟨⟨⟨⟨DegreeOneLongClass00.leaf01049_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01050_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01051_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨DegreeOneLongClass00.leaf01052_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01053_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/2) : ℚ) : ℝ)-(((37/80) : ℚ) : ℝ))*(((-116335685/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((37/80) : ℚ) : ℝ)..(((1/2) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0061Complete
