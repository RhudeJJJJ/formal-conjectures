/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00680
import Proofs.RadenkovicGutmanD1Long00Leaf00681
import Proofs.RadenkovicGutmanD1Long00Leaf00682
import Proofs.RadenkovicGutmanD1Long00Leaf00683
import Proofs.RadenkovicGutmanD1Long00Leaf00684
import Proofs.RadenkovicGutmanD1Long00Leaf00685
import Proofs.RadenkovicGutmanD1Long00Leaf00686
import Proofs.RadenkovicGutmanD1Long00Leaf00687
import Proofs.RadenkovicGutmanD1Long00Leaf00688
import Proofs.RadenkovicGutmanD1Long00Leaf00689
import Proofs.RadenkovicGutmanD1Long00Leaf00690
import Proofs.RadenkovicGutmanD1Long00Leaf00691
import Proofs.RadenkovicGutmanD1Long00Leaf00692
import Proofs.RadenkovicGutmanD1Long00Leaf00693
import Proofs.RadenkovicGutmanD1Long00Leaf00694
import Proofs.RadenkovicGutmanD1Long00Leaf00695
import Proofs.RadenkovicGutmanD1Long00Leaf00696
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0040Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00680) (.leaf DegreeOneLongClass00.leaf00681)) (.leaf DegreeOneLongClass00.leaf00682)) (.leaf DegreeOneLongClass00.leaf00683)) (.leaf DegreeOneLongClass00.leaf00684)) (.leaf DegreeOneLongClass00.leaf00685)) (.leaf DegreeOneLongClass00.leaf00686)) (.leaf DegreeOneLongClass00.leaf00687)) (.leaf DegreeOneLongClass00.leaf00688)) (.leaf DegreeOneLongClass00.leaf00689)) (.leaf DegreeOneLongClass00.leaf00690)) (.leaf DegreeOneLongClass00.leaf00691)) (.leaf DegreeOneLongClass00.leaf00692)) (.leaf DegreeOneLongClass00.leaf00693)) (.leaf DegreeOneLongClass00.leaf00694)) (.leaf DegreeOneLongClass00.leaf00695)) (.leaf DegreeOneLongClass00.leaf00696)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/160),(1/16),(-5636629637/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/160) (1/16) 0 1 0 1 (-5636629637/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00680_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00681_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00682_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00683_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00684_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00685_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00686_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00687_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00688_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00689_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00690_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00691_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00692_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00693_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00694_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00695_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00696_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/16) : ℚ) : ℝ)-(((9/160) : ℚ) : ℝ))*(((-5636629637/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/160) : ℚ) : ℝ)..(((1/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0040Complete
