/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00765
import Proofs.RadenkovicGutmanD1Long00Leaf00766
import Proofs.RadenkovicGutmanD1Long00Leaf00767
import Proofs.RadenkovicGutmanD1Long00Leaf00768
import Proofs.RadenkovicGutmanD1Long00Leaf00769
import Proofs.RadenkovicGutmanD1Long00Leaf00770
import Proofs.RadenkovicGutmanD1Long00Leaf00771
import Proofs.RadenkovicGutmanD1Long00Leaf00772
import Proofs.RadenkovicGutmanD1Long00Leaf00773
import Proofs.RadenkovicGutmanD1Long00Leaf00774
import Proofs.RadenkovicGutmanD1Long00Leaf00775
import Proofs.RadenkovicGutmanD1Long00Leaf00776
import Proofs.RadenkovicGutmanD1Long00Leaf00777
import Proofs.RadenkovicGutmanD1Long00Leaf00778
import Proofs.RadenkovicGutmanD1Long00Leaf00779
import Proofs.RadenkovicGutmanD1Long00Leaf00780
import Proofs.RadenkovicGutmanD1Long00Leaf00781
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0045Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00765) (.leaf DegreeOneLongClass00.leaf00766)) (.leaf DegreeOneLongClass00.leaf00767)) (.leaf DegreeOneLongClass00.leaf00768)) (.leaf DegreeOneLongClass00.leaf00769)) (.leaf DegreeOneLongClass00.leaf00770)) (.leaf DegreeOneLongClass00.leaf00771)) (.leaf DegreeOneLongClass00.leaf00772)) (.leaf DegreeOneLongClass00.leaf00773)) (.leaf DegreeOneLongClass00.leaf00774)) (.leaf DegreeOneLongClass00.leaf00775)) (.leaf DegreeOneLongClass00.leaf00776)) (.leaf DegreeOneLongClass00.leaf00777)) (.leaf DegreeOneLongClass00.leaf00778)) (.leaf DegreeOneLongClass00.leaf00779)) (.leaf DegreeOneLongClass00.leaf00780)) (.leaf DegreeOneLongClass00.leaf00781)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/10),(9/80),(-3511079527/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/10) (9/80) 0 1 0 1 (-3511079527/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00765_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00766_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00767_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00768_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00769_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00770_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00771_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00772_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00773_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00774_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00775_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00776_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00777_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00778_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00779_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00780_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00781_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/80) : ℚ) : ℝ)-(((1/10) : ℚ) : ℝ))*(((-3511079527/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/10) : ℚ) : ℝ)..(((9/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0045Complete
