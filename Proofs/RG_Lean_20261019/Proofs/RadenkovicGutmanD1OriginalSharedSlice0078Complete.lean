/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01326CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01327CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01328CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01329CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01330CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01331CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01332CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01333CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01334CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01335CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01336CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01337CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01338CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01339CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01340CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01341CompositionalRepair
import Proofs.RadenkovicGutmanD1Long00Leaf01342CompositionalRepair
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0078Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01326) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01327) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01328) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01329) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01330) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01331) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01332) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01333) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01334) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01335) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01336) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01337) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01338) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01339) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01340) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01341) (.leaf DegreeOneLongClass00.leaf01342))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(32/13),(8/3),(296039485/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (32/13) (8/3) 0 1 0 1 (296039485/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01326_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01327_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01328_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01329_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01330_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01331_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01332_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01333_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01334_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01335_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01336_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01337_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01338_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01339_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01340_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01341_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01342_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((8/3) : ℚ) : ℝ)-(((32/13) : ℚ) : ℝ))*(((296039485/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((32/13) : ℚ) : ℝ)..(((8/3) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0078Complete
