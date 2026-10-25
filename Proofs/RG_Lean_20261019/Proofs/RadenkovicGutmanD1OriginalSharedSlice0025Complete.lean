/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00425
import Proofs.RadenkovicGutmanD1Long00Leaf00426
import Proofs.RadenkovicGutmanD1Long00Leaf00427
import Proofs.RadenkovicGutmanD1Long00Leaf00428
import Proofs.RadenkovicGutmanD1Long00Leaf00429
import Proofs.RadenkovicGutmanD1Long00Leaf00430
import Proofs.RadenkovicGutmanD1Long00Leaf00431
import Proofs.RadenkovicGutmanD1Long00Leaf00432
import Proofs.RadenkovicGutmanD1Long00Leaf00433
import Proofs.RadenkovicGutmanD1Long00Leaf00434
import Proofs.RadenkovicGutmanD1Long00Leaf00435
import Proofs.RadenkovicGutmanD1Long00Leaf00436
import Proofs.RadenkovicGutmanD1Long00Leaf00437
import Proofs.RadenkovicGutmanD1Long00Leaf00438
import Proofs.RadenkovicGutmanD1Long00Leaf00439
import Proofs.RadenkovicGutmanD1Long00Leaf00440
import Proofs.RadenkovicGutmanD1Long00Leaf00441
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0025Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00425) (.leaf DegreeOneLongClass00.leaf00426)) (.leaf DegreeOneLongClass00.leaf00427)) (.leaf DegreeOneLongClass00.leaf00428)) (.leaf DegreeOneLongClass00.leaf00429)) (.leaf DegreeOneLongClass00.leaf00430)) (.leaf DegreeOneLongClass00.leaf00431)) (.leaf DegreeOneLongClass00.leaf00432)) (.leaf DegreeOneLongClass00.leaf00433)) (.leaf DegreeOneLongClass00.leaf00434)) (.leaf DegreeOneLongClass00.leaf00435)) (.leaf DegreeOneLongClass00.leaf00436)) (.leaf DegreeOneLongClass00.leaf00437)) (.leaf DegreeOneLongClass00.leaf00438)) (.leaf DegreeOneLongClass00.leaf00439)) (.leaf DegreeOneLongClass00.leaf00440)) (.leaf DegreeOneLongClass00.leaf00441)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/800),(1/80),(-6184407311/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/800) (1/80) 0 1 0 1 (-6184407311/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00425_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00426_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00427_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00428_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00429_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00430_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00431_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00432_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00433_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00434_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00435_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00436_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00437_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00438_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00439_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00440_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00441_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/80) : ℚ) : ℝ)-(((9/800) : ℚ) : ℝ))*(((-6184407311/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/800) : ℚ) : ℝ)..(((1/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0025Complete
