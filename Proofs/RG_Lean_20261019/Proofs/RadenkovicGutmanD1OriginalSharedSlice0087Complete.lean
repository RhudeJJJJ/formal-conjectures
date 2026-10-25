/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01479
import Proofs.RadenkovicGutmanD1Long00Leaf01480
import Proofs.RadenkovicGutmanD1Long00Leaf01481
import Proofs.RadenkovicGutmanD1Long00Leaf01482
import Proofs.RadenkovicGutmanD1Long00Leaf01483
import Proofs.RadenkovicGutmanD1Long00Leaf01484
import Proofs.RadenkovicGutmanD1Long00Leaf01485
import Proofs.RadenkovicGutmanD1Long00Leaf01486
import Proofs.RadenkovicGutmanD1Long00Leaf01487
import Proofs.RadenkovicGutmanD1Long00Leaf01488
import Proofs.RadenkovicGutmanD1Long00Leaf01489
import Proofs.RadenkovicGutmanD1Long00Leaf01490
import Proofs.RadenkovicGutmanD1Long00Leaf01491
import Proofs.RadenkovicGutmanD1Long00Leaf01492
import Proofs.RadenkovicGutmanD1Long00Leaf01493
import Proofs.RadenkovicGutmanD1Long00Leaf01494
import Proofs.RadenkovicGutmanD1Long00Leaf01495
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0087Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01479) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01480) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01481) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01482) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01483) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01484) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01485) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01486) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01487) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01488) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01489) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01490) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01491) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01492) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01493) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01494) (.leaf DegreeOneLongClass00.leaf01495))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/7),(64/13),(66955981/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/7) (64/13) 0 1 0 1 (66955981/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01479_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01480_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01481_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01482_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01483_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01484_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01485_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01486_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01487_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01488_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01489_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01490_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01491_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01492_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01493_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01494_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01495_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/13) : ℚ) : ℝ)-(((32/7) : ℚ) : ℝ))*(((66955981/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/7) : ℚ) : ℝ)..(((64/13) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0087Complete
