/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00017
import Proofs.RadenkovicGutmanD1Long00Leaf00018
import Proofs.RadenkovicGutmanD1Long00Leaf00019
import Proofs.RadenkovicGutmanD1Long00Leaf00020
import Proofs.RadenkovicGutmanD1Long00Leaf00021
import Proofs.RadenkovicGutmanD1Long00Leaf00022
import Proofs.RadenkovicGutmanD1Long00Leaf00023
import Proofs.RadenkovicGutmanD1Long00Leaf00024
import Proofs.RadenkovicGutmanD1Long00Leaf00025
import Proofs.RadenkovicGutmanD1Long00Leaf00026
import Proofs.RadenkovicGutmanD1Long00Leaf00027
import Proofs.RadenkovicGutmanD1Long00Leaf00028
import Proofs.RadenkovicGutmanD1Long00Leaf00029
import Proofs.RadenkovicGutmanD1Long00Leaf00030
import Proofs.RadenkovicGutmanD1Long00Leaf00031
import Proofs.RadenkovicGutmanD1Long00Leaf00032
import Proofs.RadenkovicGutmanD1Long00Leaf00033
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0001Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00017) (.leaf DegreeOneLongClass00.leaf00018)) (.leaf DegreeOneLongClass00.leaf00019)) (.leaf DegreeOneLongClass00.leaf00020)) (.leaf DegreeOneLongClass00.leaf00021)) (.leaf DegreeOneLongClass00.leaf00022)) (.leaf DegreeOneLongClass00.leaf00023)) (.leaf DegreeOneLongClass00.leaf00024)) (.leaf DegreeOneLongClass00.leaf00025)) (.leaf DegreeOneLongClass00.leaf00026)) (.leaf DegreeOneLongClass00.leaf00027)) (.leaf DegreeOneLongClass00.leaf00028)) (.leaf DegreeOneLongClass00.leaf00029)) (.leaf DegreeOneLongClass00.leaf00030)) (.leaf DegreeOneLongClass00.leaf00031)) (.leaf DegreeOneLongClass00.leaf00032)) (.leaf DegreeOneLongClass00.leaf00033)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/8000),(1/800),(-2791943553/536870912)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/8000) (1/800) 0 1 0 1 (-2791943553/536870912) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00017_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00018_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00019_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00020_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00021_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00022_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00023_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00024_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00025_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00026_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00027_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00028_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00029_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00030_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00031_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00032_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00033_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/800) : ℚ) : ℝ)-(((9/8000) : ℚ) : ℝ))*(((-2791943553/536870912) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/8000) : ℚ) : ℝ)..(((1/800) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0001Complete
