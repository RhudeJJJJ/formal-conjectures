/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00816
import Proofs.RadenkovicGutmanD1Long00Leaf00817
import Proofs.RadenkovicGutmanD1Long00Leaf00818
import Proofs.RadenkovicGutmanD1Long00Leaf00819
import Proofs.RadenkovicGutmanD1Long00Leaf00820
import Proofs.RadenkovicGutmanD1Long00Leaf00821
import Proofs.RadenkovicGutmanD1Long00Leaf00822
import Proofs.RadenkovicGutmanD1Long00Leaf00823
import Proofs.RadenkovicGutmanD1Long00Leaf00824
import Proofs.RadenkovicGutmanD1Long00Leaf00825
import Proofs.RadenkovicGutmanD1Long00Leaf00826
import Proofs.RadenkovicGutmanD1Long00Leaf00827
import Proofs.RadenkovicGutmanD1Long00Leaf00828
import Proofs.RadenkovicGutmanD1Long00Leaf00829
import Proofs.RadenkovicGutmanD1Long00Leaf00830
import Proofs.RadenkovicGutmanD1Long00Leaf00831
import Proofs.RadenkovicGutmanD1Long00Leaf00832
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0048Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00816) (.leaf DegreeOneLongClass00.leaf00817)) (.leaf DegreeOneLongClass00.leaf00818)) (.leaf DegreeOneLongClass00.leaf00819)) (.leaf DegreeOneLongClass00.leaf00820)) (.leaf DegreeOneLongClass00.leaf00821)) (.leaf DegreeOneLongClass00.leaf00822)) (.leaf DegreeOneLongClass00.leaf00823)) (.leaf DegreeOneLongClass00.leaf00824)) (.leaf DegreeOneLongClass00.leaf00825)) (.leaf DegreeOneLongClass00.leaf00826)) (.leaf DegreeOneLongClass00.leaf00827)) (.leaf DegreeOneLongClass00.leaf00828)) (.leaf DegreeOneLongClass00.leaf00829)) (.leaf DegreeOneLongClass00.leaf00830)) (.leaf DegreeOneLongClass00.leaf00831)) (.leaf DegreeOneLongClass00.leaf00832)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/80),(3/20),(-2508456599/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/80) (3/20) 0 1 0 1 (-2508456599/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00816_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00817_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00818_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00819_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00820_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00821_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00822_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00823_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00824_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00825_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00826_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00827_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00828_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00829_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00830_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00831_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00832_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/20) : ℚ) : ℝ)-(((11/80) : ℚ) : ℝ))*(((-2508456599/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/80) : ℚ) : ℝ)..(((3/20) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0048Complete
