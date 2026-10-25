/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00153
import Proofs.RadenkovicGutmanD1Long00Leaf00154
import Proofs.RadenkovicGutmanD1Long00Leaf00155
import Proofs.RadenkovicGutmanD1Long00Leaf00156
import Proofs.RadenkovicGutmanD1Long00Leaf00157
import Proofs.RadenkovicGutmanD1Long00Leaf00158
import Proofs.RadenkovicGutmanD1Long00Leaf00159
import Proofs.RadenkovicGutmanD1Long00Leaf00160
import Proofs.RadenkovicGutmanD1Long00Leaf00161
import Proofs.RadenkovicGutmanD1Long00Leaf00162
import Proofs.RadenkovicGutmanD1Long00Leaf00163
import Proofs.RadenkovicGutmanD1Long00Leaf00164
import Proofs.RadenkovicGutmanD1Long00Leaf00165
import Proofs.RadenkovicGutmanD1Long00Leaf00166
import Proofs.RadenkovicGutmanD1Long00Leaf00167
import Proofs.RadenkovicGutmanD1Long00Leaf00168
import Proofs.RadenkovicGutmanD1Long00Leaf00169
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0009Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00153) (.leaf DegreeOneLongClass00.leaf00154)) (.leaf DegreeOneLongClass00.leaf00155)) (.leaf DegreeOneLongClass00.leaf00156)) (.leaf DegreeOneLongClass00.leaf00157)) (.leaf DegreeOneLongClass00.leaf00158)) (.leaf DegreeOneLongClass00.leaf00159)) (.leaf DegreeOneLongClass00.leaf00160)) (.leaf DegreeOneLongClass00.leaf00161)) (.leaf DegreeOneLongClass00.leaf00162)) (.leaf DegreeOneLongClass00.leaf00163)) (.leaf DegreeOneLongClass00.leaf00164)) (.leaf DegreeOneLongClass00.leaf00165)) (.leaf DegreeOneLongClass00.leaf00166)) (.leaf DegreeOneLongClass00.leaf00167)) (.leaf DegreeOneLongClass00.leaf00168)) (.leaf DegreeOneLongClass00.leaf00169)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/4000),(1/320),(-18416985695/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/4000) (1/320) 0 1 0 1 (-18416985695/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00153_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00154_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00155_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00156_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00157_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00158_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00159_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00160_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00161_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00162_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00163_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00164_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00165_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00166_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00167_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00168_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00169_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/320) : ℚ) : ℝ)-(((11/4000) : ℚ) : ℝ))*(((-18416985695/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/4000) : ℚ) : ℝ)..(((1/320) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0009Complete
