/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00408
import Proofs.RadenkovicGutmanD1Long00Leaf00409
import Proofs.RadenkovicGutmanD1Long00Leaf00410
import Proofs.RadenkovicGutmanD1Long00Leaf00411
import Proofs.RadenkovicGutmanD1Long00Leaf00412
import Proofs.RadenkovicGutmanD1Long00Leaf00413
import Proofs.RadenkovicGutmanD1Long00Leaf00414
import Proofs.RadenkovicGutmanD1Long00Leaf00415
import Proofs.RadenkovicGutmanD1Long00Leaf00416
import Proofs.RadenkovicGutmanD1Long00Leaf00417
import Proofs.RadenkovicGutmanD1Long00Leaf00418
import Proofs.RadenkovicGutmanD1Long00Leaf00419
import Proofs.RadenkovicGutmanD1Long00Leaf00420
import Proofs.RadenkovicGutmanD1Long00Leaf00421
import Proofs.RadenkovicGutmanD1Long00Leaf00422
import Proofs.RadenkovicGutmanD1Long00Leaf00423
import Proofs.RadenkovicGutmanD1Long00Leaf00424
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0024Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00408) (.leaf DegreeOneLongClass00.leaf00409)) (.leaf DegreeOneLongClass00.leaf00410)) (.leaf DegreeOneLongClass00.leaf00411)) (.leaf DegreeOneLongClass00.leaf00412)) (.leaf DegreeOneLongClass00.leaf00413)) (.leaf DegreeOneLongClass00.leaf00414)) (.leaf DegreeOneLongClass00.leaf00415)) (.leaf DegreeOneLongClass00.leaf00416)) (.leaf DegreeOneLongClass00.leaf00417)) (.leaf DegreeOneLongClass00.leaf00418)) (.leaf DegreeOneLongClass00.leaf00419)) (.leaf DegreeOneLongClass00.leaf00420)) (.leaf DegreeOneLongClass00.leaf00421)) (.leaf DegreeOneLongClass00.leaf00422)) (.leaf DegreeOneLongClass00.leaf00423)) (.leaf DegreeOneLongClass00.leaf00424)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/100),(9/800),(-12873045655/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/100) (9/800) 0 1 0 1 (-12873045655/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00408_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00409_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00410_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00411_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00412_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00413_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00414_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00415_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00416_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00417_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00418_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00419_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00420_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00421_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00422_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00423_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00424_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/800) : ℚ) : ℝ)-(((1/100) : ℚ) : ℝ))*(((-12873045655/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/100) : ℚ) : ℝ)..(((9/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0024Complete
