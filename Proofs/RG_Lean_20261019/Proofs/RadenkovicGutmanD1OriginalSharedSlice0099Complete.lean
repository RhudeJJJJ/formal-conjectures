/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01683
import Proofs.RadenkovicGutmanD1Long00Leaf01684
import Proofs.RadenkovicGutmanD1Long00Leaf01685
import Proofs.RadenkovicGutmanD1Long00Leaf01686
import Proofs.RadenkovicGutmanD1Long00Leaf01687
import Proofs.RadenkovicGutmanD1Long00Leaf01688
import Proofs.RadenkovicGutmanD1Long00Leaf01689
import Proofs.RadenkovicGutmanD1Long00Leaf01690
import Proofs.RadenkovicGutmanD1Long00Leaf01691
import Proofs.RadenkovicGutmanD1Long00Leaf01692
import Proofs.RadenkovicGutmanD1Long00Leaf01693
import Proofs.RadenkovicGutmanD1Long00Leaf01694
import Proofs.RadenkovicGutmanD1Long00Leaf01695
import Proofs.RadenkovicGutmanD1Long00Leaf01696
import Proofs.RadenkovicGutmanD1Long00Leaf01697
import Proofs.RadenkovicGutmanD1Long00Leaf01698
import Proofs.RadenkovicGutmanD1Long00Leaf01699
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0099Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01683) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01684) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01685) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01686) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01687) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01688) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01689) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01690) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01691) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01692) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01693) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01694) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01695) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01696) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01697) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01698) (.leaf DegreeOneLongClass00.leaf01699))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/3),(128/11),(917627/134217728)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/3) (128/11) 0 1 0 1 (917627/134217728) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01683_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01684_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01685_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01686_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01687_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01688_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01689_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01690_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01691_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01692_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01693_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01694_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01695_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01696_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01697_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01698_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01699_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((128/11) : ℚ) : ℝ)-(((32/3) : ℚ) : ℝ))*(((917627/134217728) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/3) : ℚ) : ℝ)..(((128/11) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0099Complete
