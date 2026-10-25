/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01377
import Proofs.RadenkovicGutmanD1Long00Leaf01378
import Proofs.RadenkovicGutmanD1Long00Leaf01379
import Proofs.RadenkovicGutmanD1Long00Leaf01380
import Proofs.RadenkovicGutmanD1Long00Leaf01381
import Proofs.RadenkovicGutmanD1Long00Leaf01382
import Proofs.RadenkovicGutmanD1Long00Leaf01383
import Proofs.RadenkovicGutmanD1Long00Leaf01384
import Proofs.RadenkovicGutmanD1Long00Leaf01385
import Proofs.RadenkovicGutmanD1Long00Leaf01386
import Proofs.RadenkovicGutmanD1Long00Leaf01387
import Proofs.RadenkovicGutmanD1Long00Leaf01388
import Proofs.RadenkovicGutmanD1Long00Leaf01389
import Proofs.RadenkovicGutmanD1Long00Leaf01390
import Proofs.RadenkovicGutmanD1Long00Leaf01391
import Proofs.RadenkovicGutmanD1Long00Leaf01392
import Proofs.RadenkovicGutmanD1Long00Leaf01393
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0081Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01377) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01378) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01379) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01380) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01381) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01382) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01383) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01384) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01385) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01386) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01387) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01388) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01389) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01390) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01391) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01392) (.leaf DegreeOneLongClass00.leaf01393))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(16/5),(64/19),(57286115/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (16/5) (64/19) 0 1 0 1 (57286115/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01377_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01378_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01379_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01380_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01381_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01382_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01383_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01384_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01385_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01386_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01387_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01388_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01389_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01390_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01391_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01392_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01393_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/19) : ℚ) : ℝ)-(((16/5) : ℚ) : ℝ))*(((57286115/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((16/5) : ℚ) : ℝ)..(((64/19) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0081Complete
