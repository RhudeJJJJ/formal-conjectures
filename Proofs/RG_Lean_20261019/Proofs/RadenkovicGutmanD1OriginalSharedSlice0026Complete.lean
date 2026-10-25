/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00442
import Proofs.RadenkovicGutmanD1Long00Leaf00443
import Proofs.RadenkovicGutmanD1Long00Leaf00444
import Proofs.RadenkovicGutmanD1Long00Leaf00445
import Proofs.RadenkovicGutmanD1Long00Leaf00446
import Proofs.RadenkovicGutmanD1Long00Leaf00447
import Proofs.RadenkovicGutmanD1Long00Leaf00448
import Proofs.RadenkovicGutmanD1Long00Leaf00449
import Proofs.RadenkovicGutmanD1Long00Leaf00450
import Proofs.RadenkovicGutmanD1Long00Leaf00451
import Proofs.RadenkovicGutmanD1Long00Leaf00452
import Proofs.RadenkovicGutmanD1Long00Leaf00453
import Proofs.RadenkovicGutmanD1Long00Leaf00454
import Proofs.RadenkovicGutmanD1Long00Leaf00455
import Proofs.RadenkovicGutmanD1Long00Leaf00456
import Proofs.RadenkovicGutmanD1Long00Leaf00457
import Proofs.RadenkovicGutmanD1Long00Leaf00458
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0026Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00442) (.leaf DegreeOneLongClass00.leaf00443)) (.leaf DegreeOneLongClass00.leaf00444)) (.leaf DegreeOneLongClass00.leaf00445)) (.leaf DegreeOneLongClass00.leaf00446)) (.leaf DegreeOneLongClass00.leaf00447)) (.leaf DegreeOneLongClass00.leaf00448)) (.leaf DegreeOneLongClass00.leaf00449)) (.leaf DegreeOneLongClass00.leaf00450)) (.leaf DegreeOneLongClass00.leaf00451)) (.leaf DegreeOneLongClass00.leaf00452)) (.leaf DegreeOneLongClass00.leaf00453)) (.leaf DegreeOneLongClass00.leaf00454)) (.leaf DegreeOneLongClass00.leaf00455)) (.leaf DegreeOneLongClass00.leaf00456)) (.leaf DegreeOneLongClass00.leaf00457)) (.leaf DegreeOneLongClass00.leaf00458)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/80),(11/800),(-11918140865/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/80) (11/800) 0 1 0 1 (-11918140865/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00442_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00443_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00444_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00445_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00446_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00447_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00448_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00449_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00450_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00451_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00452_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00453_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00454_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00455_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00456_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00457_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00458_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/800) : ℚ) : ℝ)-(((1/80) : ℚ) : ℝ))*(((-11918140865/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/80) : ℚ) : ℝ)..(((11/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0026Complete
