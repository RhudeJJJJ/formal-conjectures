/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01530
import Proofs.RadenkovicGutmanD1Long00Leaf01531
import Proofs.RadenkovicGutmanD1Long00Leaf01532
import Proofs.RadenkovicGutmanD1Long00Leaf01533
import Proofs.RadenkovicGutmanD1Long00Leaf01534
import Proofs.RadenkovicGutmanD1Long00Leaf01535
import Proofs.RadenkovicGutmanD1Long00Leaf01536
import Proofs.RadenkovicGutmanD1Long00Leaf01537
import Proofs.RadenkovicGutmanD1Long00Leaf01538
import Proofs.RadenkovicGutmanD1Long00Leaf01539
import Proofs.RadenkovicGutmanD1Long00Leaf01540
import Proofs.RadenkovicGutmanD1Long00Leaf01541
import Proofs.RadenkovicGutmanD1Long00Leaf01542
import Proofs.RadenkovicGutmanD1Long00Leaf01543
import Proofs.RadenkovicGutmanD1Long00Leaf01544
import Proofs.RadenkovicGutmanD1Long00Leaf01545
import Proofs.RadenkovicGutmanD1Long00Leaf01546
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0090Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01530) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01531) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01532) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01533) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01534) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01535) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01536) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01537) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01538) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01539) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01540) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01541) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01542) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01543) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01544) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01545) (.leaf DegreeOneLongClass00.leaf01546))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/11),(32/5),(86942391/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (64/11) (32/5) 0 1 0 1 (86942391/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01530_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01531_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01532_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01533_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01534_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01535_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01536_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01537_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01538_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01539_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01540_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01541_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01542_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01543_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01544_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01545_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01546_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/5) : ℚ) : ℝ)-(((64/11) : ℚ) : ℝ))*(((86942391/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((64/11) : ℚ) : ℝ)..(((32/5) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0090Complete
