/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01411
import Proofs.RadenkovicGutmanD1Long00Leaf01412
import Proofs.RadenkovicGutmanD1Long00Leaf01413
import Proofs.RadenkovicGutmanD1Long00Leaf01414
import Proofs.RadenkovicGutmanD1Long00Leaf01415
import Proofs.RadenkovicGutmanD1Long00Leaf01416
import Proofs.RadenkovicGutmanD1Long00Leaf01417
import Proofs.RadenkovicGutmanD1Long00Leaf01418
import Proofs.RadenkovicGutmanD1Long00Leaf01419
import Proofs.RadenkovicGutmanD1Long00Leaf01420
import Proofs.RadenkovicGutmanD1Long00Leaf01421
import Proofs.RadenkovicGutmanD1Long00Leaf01422
import Proofs.RadenkovicGutmanD1Long00Leaf01423
import Proofs.RadenkovicGutmanD1Long00Leaf01424
import Proofs.RadenkovicGutmanD1Long00Leaf01425
import Proofs.RadenkovicGutmanD1Long00Leaf01426
import Proofs.RadenkovicGutmanD1Long00Leaf01427
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0083Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01411) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01412) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01413) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01414) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01415) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01416) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01417) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01418) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01419) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01420) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01421) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01422) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01423) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01424) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01425) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01426) (.leaf DegreeOneLongClass00.leaf01427))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/9),(64/17),(198406485/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/9) (64/17) 0 1 0 1 (198406485/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01411_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01412_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01413_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01414_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01415_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01416_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01417_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01418_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01419_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01420_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01421_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01422_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01423_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01424_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01425_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01426_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01427_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((64/17) : ℚ) : ℝ)-(((32/9) : ℚ) : ℝ))*(((198406485/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/9) : ℚ) : ℝ)..(((64/17) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0083Complete
