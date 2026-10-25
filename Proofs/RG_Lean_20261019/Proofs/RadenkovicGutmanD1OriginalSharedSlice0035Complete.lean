/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00595
import Proofs.RadenkovicGutmanD1Long00Leaf00596
import Proofs.RadenkovicGutmanD1Long00Leaf00597
import Proofs.RadenkovicGutmanD1Long00Leaf00598
import Proofs.RadenkovicGutmanD1Long00Leaf00599
import Proofs.RadenkovicGutmanD1Long00Leaf00600
import Proofs.RadenkovicGutmanD1Long00Leaf00601
import Proofs.RadenkovicGutmanD1Long00Leaf00602
import Proofs.RadenkovicGutmanD1Long00Leaf00603
import Proofs.RadenkovicGutmanD1Long00Leaf00604
import Proofs.RadenkovicGutmanD1Long00Leaf00605
import Proofs.RadenkovicGutmanD1Long00Leaf00606
import Proofs.RadenkovicGutmanD1Long00Leaf00607
import Proofs.RadenkovicGutmanD1Long00Leaf00608
import Proofs.RadenkovicGutmanD1Long00Leaf00609
import Proofs.RadenkovicGutmanD1Long00Leaf00610
import Proofs.RadenkovicGutmanD1Long00Leaf00611
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0035Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00595) (.leaf DegreeOneLongClass00.leaf00596)) (.leaf DegreeOneLongClass00.leaf00597)) (.leaf DegreeOneLongClass00.leaf00598)) (.leaf DegreeOneLongClass00.leaf00599)) (.leaf DegreeOneLongClass00.leaf00600)) (.leaf DegreeOneLongClass00.leaf00601)) (.leaf DegreeOneLongClass00.leaf00602)) (.leaf DegreeOneLongClass00.leaf00603)) (.leaf DegreeOneLongClass00.leaf00604)) (.leaf DegreeOneLongClass00.leaf00605)) (.leaf DegreeOneLongClass00.leaf00606)) (.leaf DegreeOneLongClass00.leaf00607)) (.leaf DegreeOneLongClass00.leaf00608)) (.leaf DegreeOneLongClass00.leaf00609)) (.leaf DegreeOneLongClass00.leaf00610)) (.leaf DegreeOneLongClass00.leaf00611)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/32),(7/200),(-4016666079/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/32) (7/200) 0 1 0 1 (-4016666079/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00595_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00596_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00597_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00598_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00599_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00600_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00601_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00602_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00603_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00604_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00605_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00606_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00607_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00608_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00609_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00610_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00611_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/200) : ℚ) : ℝ)-(((1/32) : ℚ) : ℝ))*(((-4016666079/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/32) : ℚ) : ℝ)..(((7/200) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0035Complete
