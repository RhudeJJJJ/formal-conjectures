/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00255
import Proofs.RadenkovicGutmanD1Long00Leaf00256
import Proofs.RadenkovicGutmanD1Long00Leaf00257
import Proofs.RadenkovicGutmanD1Long00Leaf00258
import Proofs.RadenkovicGutmanD1Long00Leaf00259
import Proofs.RadenkovicGutmanD1Long00Leaf00260
import Proofs.RadenkovicGutmanD1Long00Leaf00261
import Proofs.RadenkovicGutmanD1Long00Leaf00262
import Proofs.RadenkovicGutmanD1Long00Leaf00263
import Proofs.RadenkovicGutmanD1Long00Leaf00264
import Proofs.RadenkovicGutmanD1Long00Leaf00265
import Proofs.RadenkovicGutmanD1Long00Leaf00266
import Proofs.RadenkovicGutmanD1Long00Leaf00267
import Proofs.RadenkovicGutmanD1Long00Leaf00268
import Proofs.RadenkovicGutmanD1Long00Leaf00269
import Proofs.RadenkovicGutmanD1Long00Leaf00270
import Proofs.RadenkovicGutmanD1Long00Leaf00271
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0015Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00255) (.leaf DegreeOneLongClass00.leaf00256)) (.leaf DegreeOneLongClass00.leaf00257)) (.leaf DegreeOneLongClass00.leaf00258)) (.leaf DegreeOneLongClass00.leaf00259)) (.leaf DegreeOneLongClass00.leaf00260)) (.leaf DegreeOneLongClass00.leaf00261)) (.leaf DegreeOneLongClass00.leaf00262)) (.leaf DegreeOneLongClass00.leaf00263)) (.leaf DegreeOneLongClass00.leaf00264)) (.leaf DegreeOneLongClass00.leaf00265)) (.leaf DegreeOneLongClass00.leaf00266)) (.leaf DegreeOneLongClass00.leaf00267)) (.leaf DegreeOneLongClass00.leaf00268)) (.leaf DegreeOneLongClass00.leaf00269)) (.leaf DegreeOneLongClass00.leaf00270)) (.leaf DegreeOneLongClass00.leaf00271)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/200),(17/3200),(-15846082065/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/200) (17/3200) 0 1 0 1 (-15846082065/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00255_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00256_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00257_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00258_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00259_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00260_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00261_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00262_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00263_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00264_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00265_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00266_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00267_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00268_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00269_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00270_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00271_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/3200) : ℚ) : ℝ)-(((1/200) : ℚ) : ℝ))*(((-15846082065/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/200) : ℚ) : ℝ)..(((17/3200) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0015Complete
