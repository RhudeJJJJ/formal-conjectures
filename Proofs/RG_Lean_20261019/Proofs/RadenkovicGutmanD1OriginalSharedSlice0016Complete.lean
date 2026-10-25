/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00272
import Proofs.RadenkovicGutmanD1Long00Leaf00273
import Proofs.RadenkovicGutmanD1Long00Leaf00274
import Proofs.RadenkovicGutmanD1Long00Leaf00275
import Proofs.RadenkovicGutmanD1Long00Leaf00276
import Proofs.RadenkovicGutmanD1Long00Leaf00277
import Proofs.RadenkovicGutmanD1Long00Leaf00278
import Proofs.RadenkovicGutmanD1Long00Leaf00279
import Proofs.RadenkovicGutmanD1Long00Leaf00280
import Proofs.RadenkovicGutmanD1Long00Leaf00281
import Proofs.RadenkovicGutmanD1Long00Leaf00282
import Proofs.RadenkovicGutmanD1Long00Leaf00283
import Proofs.RadenkovicGutmanD1Long00Leaf00284
import Proofs.RadenkovicGutmanD1Long00Leaf00285
import Proofs.RadenkovicGutmanD1Long00Leaf00286
import Proofs.RadenkovicGutmanD1Long00Leaf00287
import Proofs.RadenkovicGutmanD1Long00Leaf00288
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0016Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00272) (.leaf DegreeOneLongClass00.leaf00273)) (.leaf DegreeOneLongClass00.leaf00274)) (.leaf DegreeOneLongClass00.leaf00275)) (.leaf DegreeOneLongClass00.leaf00276)) (.leaf DegreeOneLongClass00.leaf00277)) (.leaf DegreeOneLongClass00.leaf00278)) (.leaf DegreeOneLongClass00.leaf00279)) (.leaf DegreeOneLongClass00.leaf00280)) (.leaf DegreeOneLongClass00.leaf00281)) (.leaf DegreeOneLongClass00.leaf00282)) (.leaf DegreeOneLongClass00.leaf00283)) (.leaf DegreeOneLongClass00.leaf00284)) (.leaf DegreeOneLongClass00.leaf00285)) (.leaf DegreeOneLongClass00.leaf00286)) (.leaf DegreeOneLongClass00.leaf00287)) (.leaf DegreeOneLongClass00.leaf00288)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/3200),(9/1600),(-15585766643/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (17/3200) (9/1600) 0 1 0 1 (-15585766643/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00272_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00273_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00274_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00275_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00276_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00277_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00278_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00279_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00280_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00281_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00282_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00283_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00284_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00285_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00286_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00287_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00288_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/1600) : ℚ) : ℝ)-(((17/3200) : ℚ) : ℝ))*(((-15585766643/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/3200) : ℚ) : ℝ)..(((9/1600) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0016Complete
