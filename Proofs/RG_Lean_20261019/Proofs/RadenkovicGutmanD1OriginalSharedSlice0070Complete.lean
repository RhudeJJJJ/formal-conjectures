/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01190
import Proofs.RadenkovicGutmanD1Long00Leaf01191
import Proofs.RadenkovicGutmanD1Long00Leaf01192
import Proofs.RadenkovicGutmanD1Long00Leaf01193
import Proofs.RadenkovicGutmanD1Long00Leaf01194
import Proofs.RadenkovicGutmanD1Long00Leaf01195
import Proofs.RadenkovicGutmanD1Long00Leaf01196
import Proofs.RadenkovicGutmanD1Long00Leaf01197
import Proofs.RadenkovicGutmanD1Long00Leaf01198
import Proofs.RadenkovicGutmanD1Long00Leaf01199
import Proofs.RadenkovicGutmanD1Long00Leaf01200
import Proofs.RadenkovicGutmanD1Long00Leaf01201
import Proofs.RadenkovicGutmanD1Long00Leaf01202
import Proofs.RadenkovicGutmanD1Long00Leaf01203
import Proofs.RadenkovicGutmanD1Long00Leaf01204
import Proofs.RadenkovicGutmanD1Long00Leaf01205
import Proofs.RadenkovicGutmanD1Long00Leaf01206
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0070Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01190) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01191) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01192) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01193) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01194) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01195) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01196) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01197) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01198) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01199) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01200) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01201) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01202) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01203) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01204) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01205) (.leaf DegreeOneLongClass00.leaf01206))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,1,(8/7),(151448891/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 1 (8/7) 0 1 0 1 (151448891/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01190_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01191_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01192_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01193_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01194_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01195_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01196_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01197_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01198_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01199_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01200_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01201_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01202_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01203_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01204_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01205_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01206_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((8/7) : ℚ) : ℝ)-((1 : ℚ) : ℝ))*(((151448891/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in ((1 : ℚ) : ℝ)..(((8/7) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0070Complete
