/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00510
import Proofs.RadenkovicGutmanD1Long00Leaf00511
import Proofs.RadenkovicGutmanD1Long00Leaf00512
import Proofs.RadenkovicGutmanD1Long00Leaf00513
import Proofs.RadenkovicGutmanD1Long00Leaf00514
import Proofs.RadenkovicGutmanD1Long00Leaf00515
import Proofs.RadenkovicGutmanD1Long00Leaf00516
import Proofs.RadenkovicGutmanD1Long00Leaf00517
import Proofs.RadenkovicGutmanD1Long00Leaf00518
import Proofs.RadenkovicGutmanD1Long00Leaf00519
import Proofs.RadenkovicGutmanD1Long00Leaf00520
import Proofs.RadenkovicGutmanD1Long00Leaf00521
import Proofs.RadenkovicGutmanD1Long00Leaf00522
import Proofs.RadenkovicGutmanD1Long00Leaf00523
import Proofs.RadenkovicGutmanD1Long00Leaf00524
import Proofs.RadenkovicGutmanD1Long00Leaf00525
import Proofs.RadenkovicGutmanD1Long00Leaf00526
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0030Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00510) (.leaf DegreeOneLongClass00.leaf00511)) (.leaf DegreeOneLongClass00.leaf00512)) (.leaf DegreeOneLongClass00.leaf00513)) (.leaf DegreeOneLongClass00.leaf00514)) (.leaf DegreeOneLongClass00.leaf00515)) (.leaf DegreeOneLongClass00.leaf00516)) (.leaf DegreeOneLongClass00.leaf00517)) (.leaf DegreeOneLongClass00.leaf00518)) (.leaf DegreeOneLongClass00.leaf00519)) (.leaf DegreeOneLongClass00.leaf00520)) (.leaf DegreeOneLongClass00.leaf00521)) (.leaf DegreeOneLongClass00.leaf00522)) (.leaf DegreeOneLongClass00.leaf00523)) (.leaf DegreeOneLongClass00.leaf00524)) (.leaf DegreeOneLongClass00.leaf00525)) (.leaf DegreeOneLongClass00.leaf00526)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/400),(1/50),(-10482361093/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/400) (1/50) 0 1 0 1 (-10482361093/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00510_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00511_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00512_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00513_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00514_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00515_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00516_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00517_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00518_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00519_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00520_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00521_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00522_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00523_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00524_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00525_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00526_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/50) : ℚ) : ℝ)-(((7/400) : ℚ) : ℝ))*(((-10482361093/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/400) : ℚ) : ℝ)..(((1/50) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0030Complete
