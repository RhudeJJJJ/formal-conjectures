/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00629
import Proofs.RadenkovicGutmanD1Long00Leaf00630
import Proofs.RadenkovicGutmanD1Long00Leaf00631
import Proofs.RadenkovicGutmanD1Long00Leaf00632
import Proofs.RadenkovicGutmanD1Long00Leaf00633
import Proofs.RadenkovicGutmanD1Long00Leaf00634
import Proofs.RadenkovicGutmanD1Long00Leaf00635
import Proofs.RadenkovicGutmanD1Long00Leaf00636
import Proofs.RadenkovicGutmanD1Long00Leaf00637
import Proofs.RadenkovicGutmanD1Long00Leaf00638
import Proofs.RadenkovicGutmanD1Long00Leaf00639
import Proofs.RadenkovicGutmanD1Long00Leaf00640
import Proofs.RadenkovicGutmanD1Long00Leaf00641
import Proofs.RadenkovicGutmanD1Long00Leaf00642
import Proofs.RadenkovicGutmanD1Long00Leaf00643
import Proofs.RadenkovicGutmanD1Long00Leaf00644
import Proofs.RadenkovicGutmanD1Long00Leaf00645
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0037Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00629) (.leaf DegreeOneLongClass00.leaf00630)) (.leaf DegreeOneLongClass00.leaf00631)) (.leaf DegreeOneLongClass00.leaf00632)) (.leaf DegreeOneLongClass00.leaf00633)) (.leaf DegreeOneLongClass00.leaf00634)) (.leaf DegreeOneLongClass00.leaf00635)) (.leaf DegreeOneLongClass00.leaf00636)) (.leaf DegreeOneLongClass00.leaf00637)) (.leaf DegreeOneLongClass00.leaf00638)) (.leaf DegreeOneLongClass00.leaf00639)) (.leaf DegreeOneLongClass00.leaf00640)) (.leaf DegreeOneLongClass00.leaf00641)) (.leaf DegreeOneLongClass00.leaf00642)) (.leaf DegreeOneLongClass00.leaf00643)) (.leaf DegreeOneLongClass00.leaf00644)) (.leaf DegreeOneLongClass00.leaf00645)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(31/800),(17/400),(-1785258547/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (31/800) (17/400) 0 1 0 1 (-1785258547/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00629_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00630_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00631_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00632_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00633_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00634_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00635_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00636_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00637_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00638_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00639_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00640_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00641_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00642_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00643_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00644_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00645_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/400) : ℚ) : ℝ)-(((31/800) : ℚ) : ℝ))*(((-1785258547/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((31/800) : ℚ) : ℝ)..(((17/400) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0037Complete
