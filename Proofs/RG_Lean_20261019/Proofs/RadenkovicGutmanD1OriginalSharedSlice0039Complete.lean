/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00663
import Proofs.RadenkovicGutmanD1Long00Leaf00664
import Proofs.RadenkovicGutmanD1Long00Leaf00665
import Proofs.RadenkovicGutmanD1Long00Leaf00666
import Proofs.RadenkovicGutmanD1Long00Leaf00667
import Proofs.RadenkovicGutmanD1Long00Leaf00668
import Proofs.RadenkovicGutmanD1Long00Leaf00669
import Proofs.RadenkovicGutmanD1Long00Leaf00670
import Proofs.RadenkovicGutmanD1Long00Leaf00671
import Proofs.RadenkovicGutmanD1Long00Leaf00672
import Proofs.RadenkovicGutmanD1Long00Leaf00673
import Proofs.RadenkovicGutmanD1Long00Leaf00674
import Proofs.RadenkovicGutmanD1Long00Leaf00675
import Proofs.RadenkovicGutmanD1Long00Leaf00676
import Proofs.RadenkovicGutmanD1Long00Leaf00677
import Proofs.RadenkovicGutmanD1Long00Leaf00678
import Proofs.RadenkovicGutmanD1Long00Leaf00679
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0039Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00663) (.leaf DegreeOneLongClass00.leaf00664)) (.leaf DegreeOneLongClass00.leaf00665)) (.leaf DegreeOneLongClass00.leaf00666)) (.leaf DegreeOneLongClass00.leaf00667)) (.leaf DegreeOneLongClass00.leaf00668)) (.leaf DegreeOneLongClass00.leaf00669)) (.leaf DegreeOneLongClass00.leaf00670)) (.leaf DegreeOneLongClass00.leaf00671)) (.leaf DegreeOneLongClass00.leaf00672)) (.leaf DegreeOneLongClass00.leaf00673)) (.leaf DegreeOneLongClass00.leaf00674)) (.leaf DegreeOneLongClass00.leaf00675)) (.leaf DegreeOneLongClass00.leaf00676)) (.leaf DegreeOneLongClass00.leaf00677)) (.leaf DegreeOneLongClass00.leaf00678)) (.leaf DegreeOneLongClass00.leaf00679)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/20),(9/160),(-1526192639/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/20) (9/160) 0 1 0 1 (-1526192639/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00663_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00664_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00665_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00666_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00667_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00668_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00669_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00670_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00671_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00672_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00673_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00674_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00675_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00676_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00677_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00678_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00679_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/160) : ℚ) : ℝ)-(((1/20) : ℚ) : ℝ))*(((-1526192639/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/20) : ℚ) : ℝ)..(((9/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0039Complete
