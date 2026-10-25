/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01360
import Proofs.RadenkovicGutmanD1Long00Leaf01361
import Proofs.RadenkovicGutmanD1Long00Leaf01362
import Proofs.RadenkovicGutmanD1Long00Leaf01363
import Proofs.RadenkovicGutmanD1Long00Leaf01364
import Proofs.RadenkovicGutmanD1Long00Leaf01365
import Proofs.RadenkovicGutmanD1Long00Leaf01366
import Proofs.RadenkovicGutmanD1Long00Leaf01367
import Proofs.RadenkovicGutmanD1Long00Leaf01368
import Proofs.RadenkovicGutmanD1Long00Leaf01369
import Proofs.RadenkovicGutmanD1Long00Leaf01370
import Proofs.RadenkovicGutmanD1Long00Leaf01371
import Proofs.RadenkovicGutmanD1Long00Leaf01372
import Proofs.RadenkovicGutmanD1Long00Leaf01373
import Proofs.RadenkovicGutmanD1Long00Leaf01374
import Proofs.RadenkovicGutmanD1Long00Leaf01375
import Proofs.RadenkovicGutmanD1Long00Leaf01376
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0080Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01360) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01361) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01362) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01363) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01364) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01365) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01366) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01367) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01368) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01369) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01370) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01371) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01372) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01373) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01374) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01375) (.leaf DegreeOneLongClass00.leaf01376))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/11),(16/5),(243560097/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/11) (16/5) 0 1 0 1 (243560097/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01360_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01361_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01362_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01363_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01364_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01365_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01366_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01367_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01368_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01369_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01370_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01371_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01372_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01373_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01374_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01375_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01376_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((16/5) : ℚ) : ℝ)-(((32/11) : ℚ) : ℝ))*(((243560097/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/11) : ℚ) : ℝ)..(((16/5) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0080Complete
