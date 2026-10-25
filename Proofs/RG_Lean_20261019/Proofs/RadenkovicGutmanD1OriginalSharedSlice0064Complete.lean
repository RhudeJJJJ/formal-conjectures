/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01088
import Proofs.RadenkovicGutmanD1Long00Leaf01089
import Proofs.RadenkovicGutmanD1Long00Leaf01090
import Proofs.RadenkovicGutmanD1Long00Leaf01091
import Proofs.RadenkovicGutmanD1Long00Leaf01092
import Proofs.RadenkovicGutmanD1Long00Leaf01093
import Proofs.RadenkovicGutmanD1Long00Leaf01094
import Proofs.RadenkovicGutmanD1Long00Leaf01095
import Proofs.RadenkovicGutmanD1Long00Leaf01096
import Proofs.RadenkovicGutmanD1Long00Leaf01097
import Proofs.RadenkovicGutmanD1Long00Leaf01098
import Proofs.RadenkovicGutmanD1Long00Leaf01099
import Proofs.RadenkovicGutmanD1Long00Leaf01100
import Proofs.RadenkovicGutmanD1Long00Leaf01101
import Proofs.RadenkovicGutmanD1Long00Leaf01102
import Proofs.RadenkovicGutmanD1Long00Leaf01103
import Proofs.RadenkovicGutmanD1Long00Leaf01104
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0064Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01088) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01089) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01090) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01091) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01092) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01093) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01094) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01095) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01096) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01097) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01098) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01099) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01100) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01101) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01102) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01103) (.leaf DegreeOneLongClass00.leaf01104))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(5/8),(11/16),(13056323/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (5/8) (11/16) 0 1 0 1 (13056323/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01088_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01089_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01090_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01091_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01092_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01093_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01094_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01095_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01096_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01097_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01098_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01099_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01100_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01101_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01102_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01103_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01104_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/16) : ℚ) : ℝ)-(((5/8) : ℚ) : ℝ))*(((13056323/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((5/8) : ℚ) : ℝ)..(((11/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0064Complete
