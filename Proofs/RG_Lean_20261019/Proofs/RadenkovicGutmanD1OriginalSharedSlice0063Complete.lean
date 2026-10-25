/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01071
import Proofs.RadenkovicGutmanD1Long00Leaf01072
import Proofs.RadenkovicGutmanD1Long00Leaf01073
import Proofs.RadenkovicGutmanD1Long00Leaf01074
import Proofs.RadenkovicGutmanD1Long00Leaf01075
import Proofs.RadenkovicGutmanD1Long00Leaf01076
import Proofs.RadenkovicGutmanD1Long00Leaf01077
import Proofs.RadenkovicGutmanD1Long00Leaf01078
import Proofs.RadenkovicGutmanD1Long00Leaf01079
import Proofs.RadenkovicGutmanD1Long00Leaf01080
import Proofs.RadenkovicGutmanD1Long00Leaf01081
import Proofs.RadenkovicGutmanD1Long00Leaf01082
import Proofs.RadenkovicGutmanD1Long00Leaf01083
import Proofs.RadenkovicGutmanD1Long00Leaf01084
import Proofs.RadenkovicGutmanD1Long00Leaf01085
import Proofs.RadenkovicGutmanD1Long00Leaf01086
import Proofs.RadenkovicGutmanD1Long00Leaf01087
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0063Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01071) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01072) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01073) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01074) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01075) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01076) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01077) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01078) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01079) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01080) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01081) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01082) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01083) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01084) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01085) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01086) (.leaf DegreeOneLongClass00.leaf01087))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/16),(5/8),(-34950803/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/16) (5/8) 0 1 0 1 (-34950803/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01071_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01072_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01073_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01074_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01075_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01076_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01077_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01078_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01079_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01080_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01081_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01082_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01083_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01084_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01085_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01086_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01087_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((5/8) : ℚ) : ℝ)-(((9/16) : ℚ) : ℝ))*(((-34950803/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/16) : ℚ) : ℝ)..(((5/8) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0063Complete
