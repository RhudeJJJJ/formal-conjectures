/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00170
import Proofs.RadenkovicGutmanD1Long00Leaf00171
import Proofs.RadenkovicGutmanD1Long00Leaf00172
import Proofs.RadenkovicGutmanD1Long00Leaf00173
import Proofs.RadenkovicGutmanD1Long00Leaf00174
import Proofs.RadenkovicGutmanD1Long00Leaf00175
import Proofs.RadenkovicGutmanD1Long00Leaf00176
import Proofs.RadenkovicGutmanD1Long00Leaf00177
import Proofs.RadenkovicGutmanD1Long00Leaf00178
import Proofs.RadenkovicGutmanD1Long00Leaf00179
import Proofs.RadenkovicGutmanD1Long00Leaf00180
import Proofs.RadenkovicGutmanD1Long00Leaf00181
import Proofs.RadenkovicGutmanD1Long00Leaf00182
import Proofs.RadenkovicGutmanD1Long00Leaf00183
import Proofs.RadenkovicGutmanD1Long00Leaf00184
import Proofs.RadenkovicGutmanD1Long00Leaf00185
import Proofs.RadenkovicGutmanD1Long00Leaf00186
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0010Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00170) (.leaf DegreeOneLongClass00.leaf00171)) (.leaf DegreeOneLongClass00.leaf00172)) (.leaf DegreeOneLongClass00.leaf00173)) (.leaf DegreeOneLongClass00.leaf00174)) (.leaf DegreeOneLongClass00.leaf00175)) (.leaf DegreeOneLongClass00.leaf00176)) (.leaf DegreeOneLongClass00.leaf00177)) (.leaf DegreeOneLongClass00.leaf00178)) (.leaf DegreeOneLongClass00.leaf00179)) (.leaf DegreeOneLongClass00.leaf00180)) (.leaf DegreeOneLongClass00.leaf00181)) (.leaf DegreeOneLongClass00.leaf00182)) (.leaf DegreeOneLongClass00.leaf00183)) (.leaf DegreeOneLongClass00.leaf00184)) (.leaf DegreeOneLongClass00.leaf00185)) (.leaf DegreeOneLongClass00.leaf00186)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/320),(7/2000),(-8933196939/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/320) (7/2000) 0 1 0 1 (-8933196939/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00170_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00171_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00172_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00173_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00174_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00175_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00176_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00177_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00178_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00179_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00180_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00181_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00182_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00183_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00184_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00185_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00186_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/2000) : ℚ) : ℝ)-(((1/320) : ℚ) : ℝ))*(((-8933196939/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/320) : ℚ) : ℝ)..(((7/2000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0010Complete
