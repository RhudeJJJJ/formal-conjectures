/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00561
import Proofs.RadenkovicGutmanD1Long00Leaf00562
import Proofs.RadenkovicGutmanD1Long00Leaf00563
import Proofs.RadenkovicGutmanD1Long00Leaf00564
import Proofs.RadenkovicGutmanD1Long00Leaf00565
import Proofs.RadenkovicGutmanD1Long00Leaf00566
import Proofs.RadenkovicGutmanD1Long00Leaf00567
import Proofs.RadenkovicGutmanD1Long00Leaf00568
import Proofs.RadenkovicGutmanD1Long00Leaf00569
import Proofs.RadenkovicGutmanD1Long00Leaf00570
import Proofs.RadenkovicGutmanD1Long00Leaf00571
import Proofs.RadenkovicGutmanD1Long00Leaf00572
import Proofs.RadenkovicGutmanD1Long00Leaf00573
import Proofs.RadenkovicGutmanD1Long00Leaf00574
import Proofs.RadenkovicGutmanD1Long00Leaf00575
import Proofs.RadenkovicGutmanD1Long00Leaf00576
import Proofs.RadenkovicGutmanD1Long00Leaf00577
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0033Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00561) (.leaf DegreeOneLongClass00.leaf00562)) (.leaf DegreeOneLongClass00.leaf00563)) (.leaf DegreeOneLongClass00.leaf00564)) (.leaf DegreeOneLongClass00.leaf00565)) (.leaf DegreeOneLongClass00.leaf00566)) (.leaf DegreeOneLongClass00.leaf00567)) (.leaf DegreeOneLongClass00.leaf00568)) (.leaf DegreeOneLongClass00.leaf00569)) (.leaf DegreeOneLongClass00.leaf00570)) (.leaf DegreeOneLongClass00.leaf00571)) (.leaf DegreeOneLongClass00.leaf00572)) (.leaf DegreeOneLongClass00.leaf00573)) (.leaf DegreeOneLongClass00.leaf00574)) (.leaf DegreeOneLongClass00.leaf00575)) (.leaf DegreeOneLongClass00.leaf00576)) (.leaf DegreeOneLongClass00.leaf00577)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(19/800),(11/400),(-9186758575/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (19/800) (11/400) 0 1 0 1 (-9186758575/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00561_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00562_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00563_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00564_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00565_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00566_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00567_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00568_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00569_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00570_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00571_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00572_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00573_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00574_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00575_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00576_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00577_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/400) : ℚ) : ℝ)-(((19/800) : ℚ) : ℝ))*(((-9186758575/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((19/800) : ℚ) : ℝ)..(((11/400) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0033Complete
