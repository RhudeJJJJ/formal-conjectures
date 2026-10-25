/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00799
import Proofs.RadenkovicGutmanD1Long00Leaf00800
import Proofs.RadenkovicGutmanD1Long00Leaf00801
import Proofs.RadenkovicGutmanD1Long00Leaf00802
import Proofs.RadenkovicGutmanD1Long00Leaf00803
import Proofs.RadenkovicGutmanD1Long00Leaf00804
import Proofs.RadenkovicGutmanD1Long00Leaf00805
import Proofs.RadenkovicGutmanD1Long00Leaf00806
import Proofs.RadenkovicGutmanD1Long00Leaf00807
import Proofs.RadenkovicGutmanD1Long00Leaf00808
import Proofs.RadenkovicGutmanD1Long00Leaf00809
import Proofs.RadenkovicGutmanD1Long00Leaf00810
import Proofs.RadenkovicGutmanD1Long00Leaf00811
import Proofs.RadenkovicGutmanD1Long00Leaf00812
import Proofs.RadenkovicGutmanD1Long00Leaf00813
import Proofs.RadenkovicGutmanD1Long00Leaf00814
import Proofs.RadenkovicGutmanD1Long00Leaf00815
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0047Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00799) (.leaf DegreeOneLongClass00.leaf00800)) (.leaf DegreeOneLongClass00.leaf00801)) (.leaf DegreeOneLongClass00.leaf00802)) (.leaf DegreeOneLongClass00.leaf00803)) (.leaf DegreeOneLongClass00.leaf00804)) (.leaf DegreeOneLongClass00.leaf00805)) (.leaf DegreeOneLongClass00.leaf00806)) (.leaf DegreeOneLongClass00.leaf00807)) (.leaf DegreeOneLongClass00.leaf00808)) (.leaf DegreeOneLongClass00.leaf00809)) (.leaf DegreeOneLongClass00.leaf00810)) (.leaf DegreeOneLongClass00.leaf00811)) (.leaf DegreeOneLongClass00.leaf00812)) (.leaf DegreeOneLongClass00.leaf00813)) (.leaf DegreeOneLongClass00.leaf00814)) (.leaf DegreeOneLongClass00.leaf00815)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/8),(11/80),(-2792046033/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/8) (11/80) 0 1 0 1 (-2792046033/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00799_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00800_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00801_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00802_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00803_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00804_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00805_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00806_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00807_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00808_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00809_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00810_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00811_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00812_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00813_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00814_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00815_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/80) : ℚ) : ℝ)-(((1/8) : ℚ) : ℝ))*(((-2792046033/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/8) : ℚ) : ℝ)..(((11/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0047Complete
