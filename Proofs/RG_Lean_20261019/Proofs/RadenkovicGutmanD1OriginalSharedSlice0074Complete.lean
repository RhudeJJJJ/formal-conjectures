/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01258Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01259Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01260
import Proofs.RadenkovicGutmanD1Long00Leaf01261Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01262Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01263Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01264Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01265Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01266Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01267Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01268Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01269Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01270Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01271Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01272Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01273Repair
import Proofs.RadenkovicGutmanD1Long00Leaf01274Repair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0074Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01258) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01259) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01260) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01261) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01262) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01263) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01264) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01265) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01266) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01267) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01268) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01269) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01270) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01271) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01272) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01273) (.leaf DegreeOneLongClass00.leaf01274))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(16/9),2,(365499117/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (16/9) 2 0 1 0 1 (365499117/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01258_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01259_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01260_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01261_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01262_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01263_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01264_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01265_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01266_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01267_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01268_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01269_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01270_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01271_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01272_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01273_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01274_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    (((2 : ℚ) : ℝ)-(((16/9) : ℚ) : ℝ))*(((365499117/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((16/9) : ℚ) : ℝ)..((2 : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0074Complete
