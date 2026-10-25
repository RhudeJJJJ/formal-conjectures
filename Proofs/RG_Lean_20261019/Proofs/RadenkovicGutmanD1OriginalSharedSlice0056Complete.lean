/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00952
import Proofs.RadenkovicGutmanD1Long00Leaf00953
import Proofs.RadenkovicGutmanD1Long00Leaf00954
import Proofs.RadenkovicGutmanD1Long00Leaf00955
import Proofs.RadenkovicGutmanD1Long00Leaf00956
import Proofs.RadenkovicGutmanD1Long00Leaf00957
import Proofs.RadenkovicGutmanD1Long00Leaf00958
import Proofs.RadenkovicGutmanD1Long00Leaf00959
import Proofs.RadenkovicGutmanD1Long00Leaf00960
import Proofs.RadenkovicGutmanD1Long00Leaf00961
import Proofs.RadenkovicGutmanD1Long00Leaf00962
import Proofs.RadenkovicGutmanD1Long00Leaf00963
import Proofs.RadenkovicGutmanD1Long00Leaf00964
import Proofs.RadenkovicGutmanD1Long00Leaf00965
import Proofs.RadenkovicGutmanD1Long00Leaf00966
import Proofs.RadenkovicGutmanD1Long00Leaf00967
import Proofs.RadenkovicGutmanD1Long00Leaf00968
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0056Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00952) (.leaf DegreeOneLongClass00.leaf00953)) (.leaf DegreeOneLongClass00.leaf00954)) (.leaf DegreeOneLongClass00.leaf00955)) (.leaf DegreeOneLongClass00.leaf00956)) (.leaf DegreeOneLongClass00.leaf00957)) (.leaf DegreeOneLongClass00.leaf00958)) (.leaf DegreeOneLongClass00.leaf00959)) (.leaf DegreeOneLongClass00.leaf00960)) (.leaf DegreeOneLongClass00.leaf00961)) (.leaf DegreeOneLongClass00.leaf00962)) (.leaf DegreeOneLongClass00.leaf00963)) (.leaf DegreeOneLongClass00.leaf00964)) (.leaf DegreeOneLongClass00.leaf00965)) (.leaf DegreeOneLongClass00.leaf00966)) (.leaf DegreeOneLongClass00.leaf00967)) (.leaf DegreeOneLongClass00.leaf00968)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/40),(5/16),(-925810453/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/40) (5/16) 0 1 0 1 (-925810453/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00952_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00953_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00954_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00955_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00956_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00957_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00958_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00959_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00960_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00961_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00962_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00963_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00964_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00965_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00966_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00967_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00968_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((5/16) : ℚ) : ℝ)-(((11/40) : ℚ) : ℝ))*(((-925810453/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/40) : ℚ) : ℝ)..(((5/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0056Complete
