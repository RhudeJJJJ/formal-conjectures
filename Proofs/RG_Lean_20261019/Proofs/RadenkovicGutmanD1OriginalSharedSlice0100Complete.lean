/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01700
import Proofs.RadenkovicGutmanD1Long00Leaf01701
import Proofs.RadenkovicGutmanD1Long00Leaf01702
import Proofs.RadenkovicGutmanD1Long00Leaf01703
import Proofs.RadenkovicGutmanD1Long00Leaf01704
import Proofs.RadenkovicGutmanD1Long00Leaf01705
import Proofs.RadenkovicGutmanD1Long00Leaf01706
import Proofs.RadenkovicGutmanD1Long00Leaf01707
import Proofs.RadenkovicGutmanD1Long00Leaf01708
import Proofs.RadenkovicGutmanD1Long00Leaf01709
import Proofs.RadenkovicGutmanD1Long00Leaf01710
import Proofs.RadenkovicGutmanD1Long00Leaf01711
import Proofs.RadenkovicGutmanD1Long00Leaf01712
import Proofs.RadenkovicGutmanD1Long00Leaf01713
import Proofs.RadenkovicGutmanD1Long00Leaf01714
import Proofs.RadenkovicGutmanD1Long00Leaf01715
import Proofs.RadenkovicGutmanD1Long00Leaf01716
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0100Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01700) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01701) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01702) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01703) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01704) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01705) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01706) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01707) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01708) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01709) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01710) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01711) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01712) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01713) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01714) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01715) (.leaf DegreeOneLongClass00.leaf01716))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(128/11),(64/5),(24503711/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (128/11) (64/5) 0 1 0 1 (24503711/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01700_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01701_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01702_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01703_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01704_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01705_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01706_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01707_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01708_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01709_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01710_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01711_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01712_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01713_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01714_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01715_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01716_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/5) : ℚ) : ℝ)-(((128/11) : ℚ) : ℝ))*(((24503711/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((128/11) : ℚ) : ℝ)..(((64/5) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0100Complete
