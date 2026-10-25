/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01275Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01276Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01277Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01278Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01279Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01280
import Proofs.RadenkovicGutmanD1Long00Leaf01281
import Proofs.RadenkovicGutmanD1Long00Leaf01282
import Proofs.RadenkovicGutmanD1Long00Leaf01283
import Proofs.RadenkovicGutmanD1Long00Leaf01284
import Proofs.RadenkovicGutmanD1Long00Leaf01285
import Proofs.RadenkovicGutmanD1Long00Leaf01286
import Proofs.RadenkovicGutmanD1Long00Leaf01287
import Proofs.RadenkovicGutmanD1Long00Leaf01288
import Proofs.RadenkovicGutmanD1Long00Leaf01289
import Proofs.RadenkovicGutmanD1Long00Leaf01290
import Proofs.RadenkovicGutmanD1Long00Leaf01291
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0075Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01275) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01276) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01277) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01278) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01279) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01280) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01281) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01282) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01283) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01284) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01285) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01286) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01287) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01288) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01289) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01290) (.leaf DegreeOneLongClass00.leaf01291))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,2,(32/15),(353106891/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 2 (32/15) 0 1 0 1 (353106891/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01275_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01276_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01277_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01278_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01279_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01280_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01281_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01282_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01283_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01284_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01285_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01286_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01287_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01288_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01289_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01290_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01291_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((32/15) : ℚ) : ℝ)-((2 : ℚ) : ℝ))*(((353106891/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in ((2 : ℚ) : ℝ)..(((32/15) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0075Complete
