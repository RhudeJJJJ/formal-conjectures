/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00102
import Proofs.RadenkovicGutmanD1Long00Leaf00103
import Proofs.RadenkovicGutmanD1Long00Leaf00104
import Proofs.RadenkovicGutmanD1Long00Leaf00105
import Proofs.RadenkovicGutmanD1Long00Leaf00106
import Proofs.RadenkovicGutmanD1Long00Leaf00107
import Proofs.RadenkovicGutmanD1Long00Leaf00108
import Proofs.RadenkovicGutmanD1Long00Leaf00109
import Proofs.RadenkovicGutmanD1Long00Leaf00110
import Proofs.RadenkovicGutmanD1Long00Leaf00111
import Proofs.RadenkovicGutmanD1Long00Leaf00112
import Proofs.RadenkovicGutmanD1Long00Leaf00113
import Proofs.RadenkovicGutmanD1Long00Leaf00114
import Proofs.RadenkovicGutmanD1Long00Leaf00115
import Proofs.RadenkovicGutmanD1Long00Leaf00116
import Proofs.RadenkovicGutmanD1Long00Leaf00117
import Proofs.RadenkovicGutmanD1Long00Leaf00118
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0006Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00102) (.leaf DegreeOneLongClass00.leaf00103)) (.leaf DegreeOneLongClass00.leaf00104)) (.leaf DegreeOneLongClass00.leaf00105)) (.leaf DegreeOneLongClass00.leaf00106)) (.leaf DegreeOneLongClass00.leaf00107)) (.leaf DegreeOneLongClass00.leaf00108)) (.leaf DegreeOneLongClass00.leaf00109)) (.leaf DegreeOneLongClass00.leaf00110)) (.leaf DegreeOneLongClass00.leaf00111)) (.leaf DegreeOneLongClass00.leaf00112)) (.leaf DegreeOneLongClass00.leaf00113)) (.leaf DegreeOneLongClass00.leaf00114)) (.leaf DegreeOneLongClass00.leaf00115)) (.leaf DegreeOneLongClass00.leaf00116)) (.leaf DegreeOneLongClass00.leaf00117)) (.leaf DegreeOneLongClass00.leaf00118)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/3200),(19/8000),(-19406376943/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/3200) (19/8000) 0 1 0 1 (-19406376943/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00102_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00103_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00104_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00105_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00106_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00107_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00108_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00109_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00110_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00111_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00112_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00113_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00114_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00115_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00116_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00117_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00118_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((19/8000) : ℚ) : ℝ)-(((7/3200) : ℚ) : ℝ))*(((-19406376943/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/3200) : ℚ) : ℝ)..(((19/8000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0006Complete
