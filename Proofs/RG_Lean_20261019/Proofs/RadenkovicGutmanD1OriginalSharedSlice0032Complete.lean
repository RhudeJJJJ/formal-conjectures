/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00544
import Proofs.RadenkovicGutmanD1Long00Leaf00545
import Proofs.RadenkovicGutmanD1Long00Leaf00546
import Proofs.RadenkovicGutmanD1Long00Leaf00547
import Proofs.RadenkovicGutmanD1Long00Leaf00548
import Proofs.RadenkovicGutmanD1Long00Leaf00549
import Proofs.RadenkovicGutmanD1Long00Leaf00550
import Proofs.RadenkovicGutmanD1Long00Leaf00551
import Proofs.RadenkovicGutmanD1Long00Leaf00552
import Proofs.RadenkovicGutmanD1Long00Leaf00553
import Proofs.RadenkovicGutmanD1Long00Leaf00554
import Proofs.RadenkovicGutmanD1Long00Leaf00555
import Proofs.RadenkovicGutmanD1Long00Leaf00556
import Proofs.RadenkovicGutmanD1Long00Leaf00557
import Proofs.RadenkovicGutmanD1Long00Leaf00558
import Proofs.RadenkovicGutmanD1Long00Leaf00559
import Proofs.RadenkovicGutmanD1Long00Leaf00560
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0032Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00544) (.leaf DegreeOneLongClass00.leaf00545)) (.leaf DegreeOneLongClass00.leaf00546)) (.leaf DegreeOneLongClass00.leaf00547)) (.leaf DegreeOneLongClass00.leaf00548)) (.leaf DegreeOneLongClass00.leaf00549)) (.leaf DegreeOneLongClass00.leaf00550)) (.leaf DegreeOneLongClass00.leaf00551)) (.leaf DegreeOneLongClass00.leaf00552)) (.leaf DegreeOneLongClass00.leaf00553)) (.leaf DegreeOneLongClass00.leaf00554)) (.leaf DegreeOneLongClass00.leaf00555)) (.leaf DegreeOneLongClass00.leaf00556)) (.leaf DegreeOneLongClass00.leaf00557)) (.leaf DegreeOneLongClass00.leaf00558)) (.leaf DegreeOneLongClass00.leaf00559)) (.leaf DegreeOneLongClass00.leaf00560)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/320),(19/800),(-9534661965/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/320) (19/800) 0 1 0 1 (-9534661965/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00544_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00545_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00546_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00547_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00548_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00549_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00550_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00551_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00552_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00553_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00554_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00555_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00556_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00557_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00558_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00559_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00560_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((19/800) : ℚ) : ℝ)-(((7/320) : ℚ) : ℝ))*(((-9534661965/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/320) : ℚ) : ℝ)..(((19/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0032Complete
