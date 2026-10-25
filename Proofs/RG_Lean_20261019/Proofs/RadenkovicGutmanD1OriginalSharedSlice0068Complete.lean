/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01156
import Proofs.RadenkovicGutmanD1Long00Leaf01157
import Proofs.RadenkovicGutmanD1Long00Leaf01158
import Proofs.RadenkovicGutmanD1Long00Leaf01159
import Proofs.RadenkovicGutmanD1Long00Leaf01160
import Proofs.RadenkovicGutmanD1Long00Leaf01161
import Proofs.RadenkovicGutmanD1Long00Leaf01162
import Proofs.RadenkovicGutmanD1Long00Leaf01163
import Proofs.RadenkovicGutmanD1Long00Leaf01164
import Proofs.RadenkovicGutmanD1Long00Leaf01165
import Proofs.RadenkovicGutmanD1Long00Leaf01166
import Proofs.RadenkovicGutmanD1Long00Leaf01167
import Proofs.RadenkovicGutmanD1Long00Leaf01168
import Proofs.RadenkovicGutmanD1Long00Leaf01169
import Proofs.RadenkovicGutmanD1Long00Leaf01170
import Proofs.RadenkovicGutmanD1Long00Leaf01171
import Proofs.RadenkovicGutmanD1Long00Leaf01172
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0068Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01156) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01157) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01158) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01159) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01160) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01161) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01162) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01163) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01164) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01165) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01166) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01167) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01168) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01169) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01170) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01171) (.leaf DegreeOneLongClass00.leaf01172))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/8),(15/16),(119669779/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/8) (15/16) 0 1 0 1 (119669779/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01156_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01157_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01158_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01159_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01160_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01161_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01162_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01163_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01164_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01165_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01166_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01167_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01168_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01169_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01170_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01171_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01172_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((15/16) : ℚ) : ℝ)-(((7/8) : ℚ) : ℝ))*(((119669779/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/8) : ℚ) : ℝ)..(((15/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0068Complete
