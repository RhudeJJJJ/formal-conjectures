/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00612
import Proofs.RadenkovicGutmanD1Long00Leaf00613
import Proofs.RadenkovicGutmanD1Long00Leaf00614
import Proofs.RadenkovicGutmanD1Long00Leaf00615
import Proofs.RadenkovicGutmanD1Long00Leaf00616
import Proofs.RadenkovicGutmanD1Long00Leaf00617
import Proofs.RadenkovicGutmanD1Long00Leaf00618
import Proofs.RadenkovicGutmanD1Long00Leaf00619
import Proofs.RadenkovicGutmanD1Long00Leaf00620
import Proofs.RadenkovicGutmanD1Long00Leaf00621
import Proofs.RadenkovicGutmanD1Long00Leaf00622
import Proofs.RadenkovicGutmanD1Long00Leaf00623
import Proofs.RadenkovicGutmanD1Long00Leaf00624
import Proofs.RadenkovicGutmanD1Long00Leaf00625
import Proofs.RadenkovicGutmanD1Long00Leaf00626
import Proofs.RadenkovicGutmanD1Long00Leaf00627
import Proofs.RadenkovicGutmanD1Long00Leaf00628
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0036Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00612) (.leaf DegreeOneLongClass00.leaf00613)) (.leaf DegreeOneLongClass00.leaf00614)) (.leaf DegreeOneLongClass00.leaf00615)) (.leaf DegreeOneLongClass00.leaf00616)) (.leaf DegreeOneLongClass00.leaf00617)) (.leaf DegreeOneLongClass00.leaf00618)) (.leaf DegreeOneLongClass00.leaf00619)) (.leaf DegreeOneLongClass00.leaf00620)) (.leaf DegreeOneLongClass00.leaf00621)) (.leaf DegreeOneLongClass00.leaf00622)) (.leaf DegreeOneLongClass00.leaf00623)) (.leaf DegreeOneLongClass00.leaf00624)) (.leaf DegreeOneLongClass00.leaf00625)) (.leaf DegreeOneLongClass00.leaf00626)) (.leaf DegreeOneLongClass00.leaf00627)) (.leaf DegreeOneLongClass00.leaf00628)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/200),(31/800),(-7561619585/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/200) (31/800) 0 1 0 1 (-7561619585/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00612_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00613_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00614_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00615_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00616_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00617_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00618_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00619_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00620_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00621_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00622_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00623_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00624_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00625_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00626_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00627_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00628_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((31/800) : ℚ) : ℝ)-(((7/200) : ℚ) : ℝ))*(((-7561619585/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/200) : ℚ) : ℝ)..(((31/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0036Complete
