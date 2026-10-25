/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00459
import Proofs.RadenkovicGutmanD1Long00Leaf00460
import Proofs.RadenkovicGutmanD1Long00Leaf00461
import Proofs.RadenkovicGutmanD1Long00Leaf00462
import Proofs.RadenkovicGutmanD1Long00Leaf00463
import Proofs.RadenkovicGutmanD1Long00Leaf00464
import Proofs.RadenkovicGutmanD1Long00Leaf00465
import Proofs.RadenkovicGutmanD1Long00Leaf00466
import Proofs.RadenkovicGutmanD1Long00Leaf00467
import Proofs.RadenkovicGutmanD1Long00Leaf00468
import Proofs.RadenkovicGutmanD1Long00Leaf00469
import Proofs.RadenkovicGutmanD1Long00Leaf00470
import Proofs.RadenkovicGutmanD1Long00Leaf00471
import Proofs.RadenkovicGutmanD1Long00Leaf00472
import Proofs.RadenkovicGutmanD1Long00Leaf00473
import Proofs.RadenkovicGutmanD1Long00Leaf00474
import Proofs.RadenkovicGutmanD1Long00Leaf00475
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0027Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00459) (.leaf DegreeOneLongClass00.leaf00460)) (.leaf DegreeOneLongClass00.leaf00461)) (.leaf DegreeOneLongClass00.leaf00462)) (.leaf DegreeOneLongClass00.leaf00463)) (.leaf DegreeOneLongClass00.leaf00464)) (.leaf DegreeOneLongClass00.leaf00465)) (.leaf DegreeOneLongClass00.leaf00466)) (.leaf DegreeOneLongClass00.leaf00467)) (.leaf DegreeOneLongClass00.leaf00468)) (.leaf DegreeOneLongClass00.leaf00469)) (.leaf DegreeOneLongClass00.leaf00470)) (.leaf DegreeOneLongClass00.leaf00471)) (.leaf DegreeOneLongClass00.leaf00472)) (.leaf DegreeOneLongClass00.leaf00473)) (.leaf DegreeOneLongClass00.leaf00474)) (.leaf DegreeOneLongClass00.leaf00475)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/800),(3/200),(-5755415873/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/800) (3/200) 0 1 0 1 (-5755415873/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00459_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00460_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00461_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00462_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00463_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00464_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00465_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00466_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00467_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00468_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00469_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00470_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00471_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00472_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00473_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00474_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00475_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/200) : ℚ) : ℝ)-(((11/800) : ℚ) : ℝ))*(((-5755415873/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/800) : ℚ) : ℝ)..(((3/200) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0027Complete
