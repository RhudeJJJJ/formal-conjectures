/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00238
import Proofs.RadenkovicGutmanD1Long00Leaf00239
import Proofs.RadenkovicGutmanD1Long00Leaf00240
import Proofs.RadenkovicGutmanD1Long00Leaf00241
import Proofs.RadenkovicGutmanD1Long00Leaf00242
import Proofs.RadenkovicGutmanD1Long00Leaf00243
import Proofs.RadenkovicGutmanD1Long00Leaf00244
import Proofs.RadenkovicGutmanD1Long00Leaf00245
import Proofs.RadenkovicGutmanD1Long00Leaf00246
import Proofs.RadenkovicGutmanD1Long00Leaf00247
import Proofs.RadenkovicGutmanD1Long00Leaf00248
import Proofs.RadenkovicGutmanD1Long00Leaf00249
import Proofs.RadenkovicGutmanD1Long00Leaf00250
import Proofs.RadenkovicGutmanD1Long00Leaf00251
import Proofs.RadenkovicGutmanD1Long00Leaf00252
import Proofs.RadenkovicGutmanD1Long00Leaf00253
import Proofs.RadenkovicGutmanD1Long00Leaf00254
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0014Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00238) (.leaf DegreeOneLongClass00.leaf00239)) (.leaf DegreeOneLongClass00.leaf00240)) (.leaf DegreeOneLongClass00.leaf00241)) (.leaf DegreeOneLongClass00.leaf00242)) (.leaf DegreeOneLongClass00.leaf00243)) (.leaf DegreeOneLongClass00.leaf00244)) (.leaf DegreeOneLongClass00.leaf00245)) (.leaf DegreeOneLongClass00.leaf00246)) (.leaf DegreeOneLongClass00.leaf00247)) (.leaf DegreeOneLongClass00.leaf00248)) (.leaf DegreeOneLongClass00.leaf00249)) (.leaf DegreeOneLongClass00.leaf00250)) (.leaf DegreeOneLongClass00.leaf00251)) (.leaf DegreeOneLongClass00.leaf00252)) (.leaf DegreeOneLongClass00.leaf00253)) (.leaf DegreeOneLongClass00.leaf00254)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(37/8000),(1/200),(-16180896181/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (37/8000) (1/200) 0 1 0 1 (-16180896181/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00238_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00239_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00240_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00241_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00242_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00243_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00244_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00245_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00246_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00247_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00248_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00249_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00250_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00251_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00252_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00253_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00254_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/200) : ℚ) : ℝ)-(((37/8000) : ℚ) : ℝ))*(((-16180896181/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((37/8000) : ℚ) : ℝ)..(((1/200) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0014Complete
