/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01173
import Proofs.RadenkovicGutmanD1Long00Leaf01174
import Proofs.RadenkovicGutmanD1Long00Leaf01175
import Proofs.RadenkovicGutmanD1Long00Leaf01176
import Proofs.RadenkovicGutmanD1Long00Leaf01177
import Proofs.RadenkovicGutmanD1Long00Leaf01178
import Proofs.RadenkovicGutmanD1Long00Leaf01179
import Proofs.RadenkovicGutmanD1Long00Leaf01180
import Proofs.RadenkovicGutmanD1Long00Leaf01181
import Proofs.RadenkovicGutmanD1Long00Leaf01182
import Proofs.RadenkovicGutmanD1Long00Leaf01183
import Proofs.RadenkovicGutmanD1Long00Leaf01184
import Proofs.RadenkovicGutmanD1Long00Leaf01185
import Proofs.RadenkovicGutmanD1Long00Leaf01186
import Proofs.RadenkovicGutmanD1Long00Leaf01187
import Proofs.RadenkovicGutmanD1Long00Leaf01188
import Proofs.RadenkovicGutmanD1Long00Leaf01189
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0069Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01173) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01174) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01175) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01176) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01177) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01178) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01179) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01180) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01181) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01182) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01183) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01184) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01185) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01186) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01187) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01188) (.leaf DegreeOneLongClass00.leaf01189))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(15/16),1,(274779195/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (15/16) 1 0 1 0 1 (274779195/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01173_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01174_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01175_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01176_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01177_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01178_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01179_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01180_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01181_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01182_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01183_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01184_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01185_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01186_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01187_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01188_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01189_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    (((1 : ℚ) : ℝ)-(((15/16) : ℚ) : ℝ))*(((274779195/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((15/16) : ℚ) : ℝ)..((1 : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0069Complete
