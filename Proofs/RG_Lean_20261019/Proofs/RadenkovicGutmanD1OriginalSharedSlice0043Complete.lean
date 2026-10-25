/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00731
import Proofs.RadenkovicGutmanD1Long00Leaf00732
import Proofs.RadenkovicGutmanD1Long00Leaf00733
import Proofs.RadenkovicGutmanD1Long00Leaf00734
import Proofs.RadenkovicGutmanD1Long00Leaf00735
import Proofs.RadenkovicGutmanD1Long00Leaf00736
import Proofs.RadenkovicGutmanD1Long00Leaf00737
import Proofs.RadenkovicGutmanD1Long00Leaf00738
import Proofs.RadenkovicGutmanD1Long00Leaf00739
import Proofs.RadenkovicGutmanD1Long00Leaf00740
import Proofs.RadenkovicGutmanD1Long00Leaf00741
import Proofs.RadenkovicGutmanD1Long00Leaf00742
import Proofs.RadenkovicGutmanD1Long00Leaf00743
import Proofs.RadenkovicGutmanD1Long00Leaf00744
import Proofs.RadenkovicGutmanD1Long00Leaf00745
import Proofs.RadenkovicGutmanD1Long00Leaf00746
import Proofs.RadenkovicGutmanD1Long00Leaf00747
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0043Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00731) (.leaf DegreeOneLongClass00.leaf00732)) (.leaf DegreeOneLongClass00.leaf00733)) (.leaf DegreeOneLongClass00.leaf00734)) (.leaf DegreeOneLongClass00.leaf00735)) (.leaf DegreeOneLongClass00.leaf00736)) (.leaf DegreeOneLongClass00.leaf00737)) (.leaf DegreeOneLongClass00.leaf00738)) (.leaf DegreeOneLongClass00.leaf00739)) (.leaf DegreeOneLongClass00.leaf00740)) (.leaf DegreeOneLongClass00.leaf00741)) (.leaf DegreeOneLongClass00.leaf00742)) (.leaf DegreeOneLongClass00.leaf00743)) (.leaf DegreeOneLongClass00.leaf00744)) (.leaf DegreeOneLongClass00.leaf00745)) (.leaf DegreeOneLongClass00.leaf00746)) (.leaf DegreeOneLongClass00.leaf00747)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/40),(7/80),(-4534031133/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/40) (7/80) 0 1 0 1 (-4534031133/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00731_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00732_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00733_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00734_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00735_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00736_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00737_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00738_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00739_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00740_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00741_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00742_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00743_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00744_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00745_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00746_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00747_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/80) : ℚ) : ℝ)-(((3/40) : ℚ) : ℝ))*(((-4534031133/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/40) : ℚ) : ℝ)..(((7/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0043Complete
