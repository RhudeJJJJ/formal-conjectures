/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00578
import Proofs.RadenkovicGutmanD1Long00Leaf00579
import Proofs.RadenkovicGutmanD1Long00Leaf00580
import Proofs.RadenkovicGutmanD1Long00Leaf00581
import Proofs.RadenkovicGutmanD1Long00Leaf00582
import Proofs.RadenkovicGutmanD1Long00Leaf00583
import Proofs.RadenkovicGutmanD1Long00Leaf00584
import Proofs.RadenkovicGutmanD1Long00Leaf00585
import Proofs.RadenkovicGutmanD1Long00Leaf00586
import Proofs.RadenkovicGutmanD1Long00Leaf00587
import Proofs.RadenkovicGutmanD1Long00Leaf00588
import Proofs.RadenkovicGutmanD1Long00Leaf00589
import Proofs.RadenkovicGutmanD1Long00Leaf00590
import Proofs.RadenkovicGutmanD1Long00Leaf00591
import Proofs.RadenkovicGutmanD1Long00Leaf00592
import Proofs.RadenkovicGutmanD1Long00Leaf00593
import Proofs.RadenkovicGutmanD1Long00Leaf00594
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0034Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00578) (.leaf DegreeOneLongClass00.leaf00579)) (.leaf DegreeOneLongClass00.leaf00580)) (.leaf DegreeOneLongClass00.leaf00581)) (.leaf DegreeOneLongClass00.leaf00582)) (.leaf DegreeOneLongClass00.leaf00583)) (.leaf DegreeOneLongClass00.leaf00584)) (.leaf DegreeOneLongClass00.leaf00585)) (.leaf DegreeOneLongClass00.leaf00586)) (.leaf DegreeOneLongClass00.leaf00587)) (.leaf DegreeOneLongClass00.leaf00588)) (.leaf DegreeOneLongClass00.leaf00589)) (.leaf DegreeOneLongClass00.leaf00590)) (.leaf DegreeOneLongClass00.leaf00591)) (.leaf DegreeOneLongClass00.leaf00592)) (.leaf DegreeOneLongClass00.leaf00593)) (.leaf DegreeOneLongClass00.leaf00594)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/400),(1/32),(-8568924623/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/400) (1/32) 0 1 0 1 (-8568924623/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00578_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00579_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00580_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00581_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00582_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00583_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00584_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00585_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00586_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00587_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00588_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00589_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00590_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00591_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00592_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00593_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00594_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/32) : ℚ) : ℝ)-(((11/400) : ℚ) : ℝ))*(((-8568924623/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/400) : ℚ) : ℝ)..(((1/32) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0034Complete
