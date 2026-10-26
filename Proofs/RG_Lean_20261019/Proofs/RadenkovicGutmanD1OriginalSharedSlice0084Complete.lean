/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01428Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01429Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01430Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01431Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01432Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01433Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01434Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01435Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01436Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01437Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01438Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01439Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01440Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01441Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01442Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01443Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01444Repair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0084Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01428) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01429) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01430) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01431) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01432) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01433) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01434) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01435) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01436) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01437) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01438) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01439) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01440) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01441) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01442) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01443) (.leaf DegreeOneLongClass00.leaf01444))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/17),4,(91248465/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/17) 4 0 1 0 1 (91248465/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01428_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01429_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01430_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01431_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01432_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01433_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01434_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01435_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01436_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01437_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01438_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01439_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01440_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01441_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01442_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01443_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01444_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    (((4 : ℚ) : ℝ)-(((64/17) : ℚ) : ℝ))*(((91248465/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/17) : ℚ) : ℝ)..((4 : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0084Complete
