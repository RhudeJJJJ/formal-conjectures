/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00646
import Proofs.RadenkovicGutmanD1Long00Leaf00647
import Proofs.RadenkovicGutmanD1Long00Leaf00648
import Proofs.RadenkovicGutmanD1Long00Leaf00649
import Proofs.RadenkovicGutmanD1Long00Leaf00650
import Proofs.RadenkovicGutmanD1Long00Leaf00651
import Proofs.RadenkovicGutmanD1Long00Leaf00652
import Proofs.RadenkovicGutmanD1Long00Leaf00653
import Proofs.RadenkovicGutmanD1Long00Leaf00654
import Proofs.RadenkovicGutmanD1Long00Leaf00655
import Proofs.RadenkovicGutmanD1Long00Leaf00656
import Proofs.RadenkovicGutmanD1Long00Leaf00657
import Proofs.RadenkovicGutmanD1Long00Leaf00658
import Proofs.RadenkovicGutmanD1Long00Leaf00659
import Proofs.RadenkovicGutmanD1Long00Leaf00660
import Proofs.RadenkovicGutmanD1Long00Leaf00661
import Proofs.RadenkovicGutmanD1Long00Leaf00662
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0038Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00646) (.leaf DegreeOneLongClass00.leaf00647)) (.leaf DegreeOneLongClass00.leaf00648)) (.leaf DegreeOneLongClass00.leaf00649)) (.leaf DegreeOneLongClass00.leaf00650)) (.leaf DegreeOneLongClass00.leaf00651)) (.leaf DegreeOneLongClass00.leaf00652)) (.leaf DegreeOneLongClass00.leaf00653)) (.leaf DegreeOneLongClass00.leaf00654)) (.leaf DegreeOneLongClass00.leaf00655)) (.leaf DegreeOneLongClass00.leaf00656)) (.leaf DegreeOneLongClass00.leaf00657)) (.leaf DegreeOneLongClass00.leaf00658)) (.leaf DegreeOneLongClass00.leaf00659)) (.leaf DegreeOneLongClass00.leaf00660)) (.leaf DegreeOneLongClass00.leaf00661)) (.leaf DegreeOneLongClass00.leaf00662)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/400),(1/20),(-3381214753/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (17/400) (1/20) 0 1 0 1 (-3381214753/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00646_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00647_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00648_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00649_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00650_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00651_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00652_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00653_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00654_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00655_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00656_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00657_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00658_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00659_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00660_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00661_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00662_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/20) : ℚ) : ℝ)-(((17/400) : ℚ) : ℝ))*(((-3381214753/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/400) : ℚ) : ℝ)..(((1/20) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0038Complete
