/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00986
import Proofs.RadenkovicGutmanD1Long00Leaf00987
import Proofs.RadenkovicGutmanD1Long00Leaf00988
import Proofs.RadenkovicGutmanD1Long00Leaf00989
import Proofs.RadenkovicGutmanD1Long00Leaf00990
import Proofs.RadenkovicGutmanD1Long00Leaf00991
import Proofs.RadenkovicGutmanD1Long00Leaf00992
import Proofs.RadenkovicGutmanD1Long00Leaf00993
import Proofs.RadenkovicGutmanD1Long00Leaf00994
import Proofs.RadenkovicGutmanD1Long00Leaf00995
import Proofs.RadenkovicGutmanD1Long00Leaf00996
import Proofs.RadenkovicGutmanD1Long00Leaf00997
import Proofs.RadenkovicGutmanD1Long00Leaf00998
import Proofs.RadenkovicGutmanD1Long00Leaf00999
import Proofs.RadenkovicGutmanD1Long00Leaf01000
import Proofs.RadenkovicGutmanD1Long00Leaf01001
import Proofs.RadenkovicGutmanD1Long00Leaf01002
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0058Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00986) (.leaf DegreeOneLongClass00.leaf00987)) (.leaf DegreeOneLongClass00.leaf00988)) (.leaf DegreeOneLongClass00.leaf00989)) (.leaf DegreeOneLongClass00.leaf00990)) (.leaf DegreeOneLongClass00.leaf00991)) (.leaf DegreeOneLongClass00.leaf00992)) (.leaf DegreeOneLongClass00.leaf00993)) (.leaf DegreeOneLongClass00.leaf00994)) (.leaf DegreeOneLongClass00.leaf00995)) (.leaf DegreeOneLongClass00.leaf00996)) (.leaf DegreeOneLongClass00.leaf00997)) (.leaf DegreeOneLongClass00.leaf00998)) (.leaf DegreeOneLongClass00.leaf00999)) (.leaf DegreeOneLongClass00.leaf01000)) (.leaf DegreeOneLongClass00.leaf01001)) (.leaf DegreeOneLongClass00.leaf01002)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/20),(31/80),(-561087545/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/20) (31/80) 0 1 0 1 (-561087545/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00986_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00987_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00988_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00989_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00990_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00991_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00992_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00993_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00994_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00995_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00996_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00997_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00998_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00999_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01000_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01001_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf01002_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((31/80) : ℚ) : ℝ)-(((7/20) : ℚ) : ℝ))*(((-561087545/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/20) : ℚ) : ℝ)..(((31/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0058Complete
