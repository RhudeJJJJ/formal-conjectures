/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01581
import Proofs.RadenkovicGutmanD1Long00Leaf01582
import Proofs.RadenkovicGutmanD1Long00Leaf01583
import Proofs.RadenkovicGutmanD1Long00Leaf01584
import Proofs.RadenkovicGutmanD1Long00Leaf01585
import Proofs.RadenkovicGutmanD1Long00Leaf01586
import Proofs.RadenkovicGutmanD1Long00Leaf01587
import Proofs.RadenkovicGutmanD1Long00Leaf01588
import Proofs.RadenkovicGutmanD1Long00Leaf01589
import Proofs.RadenkovicGutmanD1Long00Leaf01590
import Proofs.RadenkovicGutmanD1Long00Leaf01591
import Proofs.RadenkovicGutmanD1Long00Leaf01592
import Proofs.RadenkovicGutmanD1Long00Leaf01593
import Proofs.RadenkovicGutmanD1Long00Leaf01594
import Proofs.RadenkovicGutmanD1Long00Leaf01595
import Proofs.RadenkovicGutmanD1Long00Leaf01596
import Proofs.RadenkovicGutmanD1Long00Leaf01597
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0093Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01581) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01582) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01583) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01584) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01585) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01586) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01587) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01588) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01589) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01590) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01591) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01592) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01593) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01594) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01595) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01596) (.leaf DegreeOneLongClass00.leaf01597))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/9),(128/17),(8184055/536870912)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/9) (128/17) 0 1 0 1 (8184055/536870912) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01581_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01582_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01583_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01584_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01585_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01586_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01587_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01588_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01589_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01590_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01591_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01592_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01593_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01594_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01595_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01596_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01597_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/17) : ℚ) : ℝ)-(((64/9) : ℚ) : ℝ))*(((8184055/536870912) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/9) : ℚ) : ℝ)..(((128/17) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0093Complete
