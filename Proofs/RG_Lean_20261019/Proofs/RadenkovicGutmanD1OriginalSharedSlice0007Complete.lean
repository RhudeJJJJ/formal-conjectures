/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00119
import Proofs.RadenkovicGutmanD1Long00Leaf00120
import Proofs.RadenkovicGutmanD1Long00Leaf00121
import Proofs.RadenkovicGutmanD1Long00Leaf00122
import Proofs.RadenkovicGutmanD1Long00Leaf00123
import Proofs.RadenkovicGutmanD1Long00Leaf00124
import Proofs.RadenkovicGutmanD1Long00Leaf00125
import Proofs.RadenkovicGutmanD1Long00Leaf00126
import Proofs.RadenkovicGutmanD1Long00Leaf00127
import Proofs.RadenkovicGutmanD1Long00Leaf00128
import Proofs.RadenkovicGutmanD1Long00Leaf00129
import Proofs.RadenkovicGutmanD1Long00Leaf00130
import Proofs.RadenkovicGutmanD1Long00Leaf00131
import Proofs.RadenkovicGutmanD1Long00Leaf00132
import Proofs.RadenkovicGutmanD1Long00Leaf00133
import Proofs.RadenkovicGutmanD1Long00Leaf00134
import Proofs.RadenkovicGutmanD1Long00Leaf00135
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0007Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00119) (.leaf DegreeOneLongClass00.leaf00120)) (.leaf DegreeOneLongClass00.leaf00121)) (.leaf DegreeOneLongClass00.leaf00122)) (.leaf DegreeOneLongClass00.leaf00123)) (.leaf DegreeOneLongClass00.leaf00124)) (.leaf DegreeOneLongClass00.leaf00125)) (.leaf DegreeOneLongClass00.leaf00126)) (.leaf DegreeOneLongClass00.leaf00127)) (.leaf DegreeOneLongClass00.leaf00128)) (.leaf DegreeOneLongClass00.leaf00129)) (.leaf DegreeOneLongClass00.leaf00130)) (.leaf DegreeOneLongClass00.leaf00131)) (.leaf DegreeOneLongClass00.leaf00132)) (.leaf DegreeOneLongClass00.leaf00133)) (.leaf DegreeOneLongClass00.leaf00134)) (.leaf DegreeOneLongClass00.leaf00135)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(19/8000),(41/16000),(-9525259205/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (19/8000) (41/16000) 0 1 0 1 (-9525259205/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00119_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00120_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00121_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00122_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00123_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00124_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00125_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00126_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00127_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00128_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00129_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00130_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00131_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00132_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00133_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00134_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00135_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((41/16000) : ℚ) : ℝ)-(((19/8000) : ℚ) : ℝ))*(((-9525259205/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((19/8000) : ℚ) : ℝ)..(((41/16000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0007Complete
