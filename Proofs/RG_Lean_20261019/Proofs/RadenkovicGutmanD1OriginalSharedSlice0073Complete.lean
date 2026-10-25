/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01241
import Proofs.RadenkovicGutmanD1Long00Leaf01242
import Proofs.RadenkovicGutmanD1Long00Leaf01243
import Proofs.RadenkovicGutmanD1Long00Leaf01244
import Proofs.RadenkovicGutmanD1Long00Leaf01245
import Proofs.RadenkovicGutmanD1Long00Leaf01246
import Proofs.RadenkovicGutmanD1Long00Leaf01247
import Proofs.RadenkovicGutmanD1Long00Leaf01248
import Proofs.RadenkovicGutmanD1Long00Leaf01249
import Proofs.RadenkovicGutmanD1Long00Leaf01250
import Proofs.RadenkovicGutmanD1Long00Leaf01251
import Proofs.RadenkovicGutmanD1Long00Leaf01252
import Proofs.RadenkovicGutmanD1Long00Leaf01253
import Proofs.RadenkovicGutmanD1Long00Leaf01254
import Proofs.RadenkovicGutmanD1Long00Leaf01255
import Proofs.RadenkovicGutmanD1Long00Leaf01256
import Proofs.RadenkovicGutmanD1Long00Leaf01257
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0073Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01241) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01242) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01243) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01244) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01245) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01246) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01247) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01248) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01249) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01250) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01251) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01252) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01253) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01254) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01255) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01256) (.leaf DegreeOneLongClass00.leaf01257))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(8/5),(16/9),(383396277/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (8/5) (16/9) 0 1 0 1 (383396277/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01241_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01242_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01243_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01244_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01245_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01246_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01247_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01248_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01249_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01250_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01251_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01252_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01253_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01254_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01255_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01256_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01257_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((16/9) : ℚ) : ℝ)-(((8/5) : ℚ) : ℝ))*(((383396277/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((8/5) : ℚ) : ℝ)..(((16/9) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0073Complete
