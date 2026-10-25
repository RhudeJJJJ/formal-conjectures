/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00221
import Proofs.RadenkovicGutmanD1Long00Leaf00222
import Proofs.RadenkovicGutmanD1Long00Leaf00223
import Proofs.RadenkovicGutmanD1Long00Leaf00224
import Proofs.RadenkovicGutmanD1Long00Leaf00225
import Proofs.RadenkovicGutmanD1Long00Leaf00226
import Proofs.RadenkovicGutmanD1Long00Leaf00227
import Proofs.RadenkovicGutmanD1Long00Leaf00228
import Proofs.RadenkovicGutmanD1Long00Leaf00229
import Proofs.RadenkovicGutmanD1Long00Leaf00230
import Proofs.RadenkovicGutmanD1Long00Leaf00231
import Proofs.RadenkovicGutmanD1Long00Leaf00232
import Proofs.RadenkovicGutmanD1Long00Leaf00233
import Proofs.RadenkovicGutmanD1Long00Leaf00234
import Proofs.RadenkovicGutmanD1Long00Leaf00235
import Proofs.RadenkovicGutmanD1Long00Leaf00236
import Proofs.RadenkovicGutmanD1Long00Leaf00237
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0013Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00221) (.leaf DegreeOneLongClass00.leaf00222)) (.leaf DegreeOneLongClass00.leaf00223)) (.leaf DegreeOneLongClass00.leaf00224)) (.leaf DegreeOneLongClass00.leaf00225)) (.leaf DegreeOneLongClass00.leaf00226)) (.leaf DegreeOneLongClass00.leaf00227)) (.leaf DegreeOneLongClass00.leaf00228)) (.leaf DegreeOneLongClass00.leaf00229)) (.leaf DegreeOneLongClass00.leaf00230)) (.leaf DegreeOneLongClass00.leaf00231)) (.leaf DegreeOneLongClass00.leaf00232)) (.leaf DegreeOneLongClass00.leaf00233)) (.leaf DegreeOneLongClass00.leaf00234)) (.leaf DegreeOneLongClass00.leaf00235)) (.leaf DegreeOneLongClass00.leaf00236)) (.leaf DegreeOneLongClass00.leaf00237)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/4000),(37/8000),(-16544158983/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (17/4000) (37/8000) 0 1 0 1 (-16544158983/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00221_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00222_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00223_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00224_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00225_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00226_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00227_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00228_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00229_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00230_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00231_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00232_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00233_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00234_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00235_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00236_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00237_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((37/8000) : ℚ) : ℝ)-(((17/4000) : ℚ) : ℝ))*(((-16544158983/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/4000) : ℚ) : ℝ)..(((37/8000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0013Complete
