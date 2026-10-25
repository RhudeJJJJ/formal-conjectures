/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00850
import Proofs.RadenkovicGutmanD1Long00Leaf00851
import Proofs.RadenkovicGutmanD1Long00Leaf00852
import Proofs.RadenkovicGutmanD1Long00Leaf00853
import Proofs.RadenkovicGutmanD1Long00Leaf00854
import Proofs.RadenkovicGutmanD1Long00Leaf00855
import Proofs.RadenkovicGutmanD1Long00Leaf00856
import Proofs.RadenkovicGutmanD1Long00Leaf00857
import Proofs.RadenkovicGutmanD1Long00Leaf00858
import Proofs.RadenkovicGutmanD1Long00Leaf00859
import Proofs.RadenkovicGutmanD1Long00Leaf00860
import Proofs.RadenkovicGutmanD1Long00Leaf00861
import Proofs.RadenkovicGutmanD1Long00Leaf00862
import Proofs.RadenkovicGutmanD1Long00Leaf00863
import Proofs.RadenkovicGutmanD1Long00Leaf00864
import Proofs.RadenkovicGutmanD1Long00Leaf00865
import Proofs.RadenkovicGutmanD1Long00Leaf00866
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0050Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00850) (.leaf DegreeOneLongClass00.leaf00851)) (.leaf DegreeOneLongClass00.leaf00852)) (.leaf DegreeOneLongClass00.leaf00853)) (.leaf DegreeOneLongClass00.leaf00854)) (.leaf DegreeOneLongClass00.leaf00855)) (.leaf DegreeOneLongClass00.leaf00856)) (.leaf DegreeOneLongClass00.leaf00857)) (.leaf DegreeOneLongClass00.leaf00858)) (.leaf DegreeOneLongClass00.leaf00859)) (.leaf DegreeOneLongClass00.leaf00860)) (.leaf DegreeOneLongClass00.leaf00861)) (.leaf DegreeOneLongClass00.leaf00862)) (.leaf DegreeOneLongClass00.leaf00863)) (.leaf DegreeOneLongClass00.leaf00864)) (.leaf DegreeOneLongClass00.leaf00865)) (.leaf DegreeOneLongClass00.leaf00866)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(13/80),(7/40),(-256085721/536870912)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (13/80) (7/40) 0 1 0 1 (-256085721/536870912) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00850_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00851_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00852_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00853_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00854_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00855_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00856_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00857_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00858_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00859_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00860_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00861_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00862_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00863_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00864_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00865_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00866_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/40) : ℚ) : ℝ)-(((13/80) : ℚ) : ℝ))*(((-256085721/536870912) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((13/80) : ℚ) : ℝ)..(((7/40) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0050Complete
