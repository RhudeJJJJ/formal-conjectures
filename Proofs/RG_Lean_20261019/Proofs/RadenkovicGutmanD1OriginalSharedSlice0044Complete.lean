/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00748
import Proofs.RadenkovicGutmanD1Long00Leaf00749
import Proofs.RadenkovicGutmanD1Long00Leaf00750
import Proofs.RadenkovicGutmanD1Long00Leaf00751
import Proofs.RadenkovicGutmanD1Long00Leaf00752
import Proofs.RadenkovicGutmanD1Long00Leaf00753
import Proofs.RadenkovicGutmanD1Long00Leaf00754
import Proofs.RadenkovicGutmanD1Long00Leaf00755
import Proofs.RadenkovicGutmanD1Long00Leaf00756
import Proofs.RadenkovicGutmanD1Long00Leaf00757
import Proofs.RadenkovicGutmanD1Long00Leaf00758
import Proofs.RadenkovicGutmanD1Long00Leaf00759
import Proofs.RadenkovicGutmanD1Long00Leaf00760
import Proofs.RadenkovicGutmanD1Long00Leaf00761
import Proofs.RadenkovicGutmanD1Long00Leaf00762
import Proofs.RadenkovicGutmanD1Long00Leaf00763
import Proofs.RadenkovicGutmanD1Long00Leaf00764
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0044Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00748) (.leaf DegreeOneLongClass00.leaf00749)) (.leaf DegreeOneLongClass00.leaf00750)) (.leaf DegreeOneLongClass00.leaf00751)) (.leaf DegreeOneLongClass00.leaf00752)) (.leaf DegreeOneLongClass00.leaf00753)) (.leaf DegreeOneLongClass00.leaf00754)) (.leaf DegreeOneLongClass00.leaf00755)) (.leaf DegreeOneLongClass00.leaf00756)) (.leaf DegreeOneLongClass00.leaf00757)) (.leaf DegreeOneLongClass00.leaf00758)) (.leaf DegreeOneLongClass00.leaf00759)) (.leaf DegreeOneLongClass00.leaf00760)) (.leaf DegreeOneLongClass00.leaf00761)) (.leaf DegreeOneLongClass00.leaf00762)) (.leaf DegreeOneLongClass00.leaf00763)) (.leaf DegreeOneLongClass00.leaf00764)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/80),(1/10),(-3974037605/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/80) (1/10) 0 1 0 1 (-3974037605/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00748_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00749_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00750_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00751_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00752_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00753_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00754_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00755_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00756_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00757_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00758_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00759_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00760_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00761_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00762_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00763_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00764_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/10) : ℚ) : ℝ)-(((7/80) : ℚ) : ℝ))*(((-3974037605/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/80) : ℚ) : ℝ)..(((1/10) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0044Complete
