/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00884
import Proofs.RadenkovicGutmanD1Long00Leaf00885
import Proofs.RadenkovicGutmanD1Long00Leaf00886
import Proofs.RadenkovicGutmanD1Long00Leaf00887
import Proofs.RadenkovicGutmanD1Long00Leaf00888
import Proofs.RadenkovicGutmanD1Long00Leaf00889
import Proofs.RadenkovicGutmanD1Long00Leaf00890
import Proofs.RadenkovicGutmanD1Long00Leaf00891
import Proofs.RadenkovicGutmanD1Long00Leaf00892
import Proofs.RadenkovicGutmanD1Long00Leaf00893
import Proofs.RadenkovicGutmanD1Long00Leaf00894
import Proofs.RadenkovicGutmanD1Long00Leaf00895
import Proofs.RadenkovicGutmanD1Long00Leaf00896
import Proofs.RadenkovicGutmanD1Long00Leaf00897
import Proofs.RadenkovicGutmanD1Long00Leaf00898
import Proofs.RadenkovicGutmanD1Long00Leaf00899
import Proofs.RadenkovicGutmanD1Long00Leaf00900
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0052Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00884) (.leaf DegreeOneLongClass00.leaf00885)) (.leaf DegreeOneLongClass00.leaf00886)) (.leaf DegreeOneLongClass00.leaf00887)) (.leaf DegreeOneLongClass00.leaf00888)) (.leaf DegreeOneLongClass00.leaf00889)) (.leaf DegreeOneLongClass00.leaf00890)) (.leaf DegreeOneLongClass00.leaf00891)) (.leaf DegreeOneLongClass00.leaf00892)) (.leaf DegreeOneLongClass00.leaf00893)) (.leaf DegreeOneLongClass00.leaf00894)) (.leaf DegreeOneLongClass00.leaf00895)) (.leaf DegreeOneLongClass00.leaf00896)) (.leaf DegreeOneLongClass00.leaf00897)) (.leaf DegreeOneLongClass00.leaf00898)) (.leaf DegreeOneLongClass00.leaf00899)) (.leaf DegreeOneLongClass00.leaf00900)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/5),(7/32),(-386727571/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/5) (7/32) 0 1 0 1 (-386727571/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00884_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00885_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00886_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00887_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00888_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00889_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00890_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00891_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00892_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00893_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00894_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00895_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00896_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00897_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00898_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00899_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00900_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/32) : ℚ) : ℝ)-(((1/5) : ℚ) : ℝ))*(((-386727571/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/5) : ℚ) : ℝ)..(((7/32) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0052Complete
