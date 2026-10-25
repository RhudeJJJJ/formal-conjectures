/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01054
import Proofs.RadenkovicGutmanD1Long00Leaf01055
import Proofs.RadenkovicGutmanD1Long00Leaf01056
import Proofs.RadenkovicGutmanD1Long00Leaf01057
import Proofs.RadenkovicGutmanD1Long00Leaf01058
import Proofs.RadenkovicGutmanD1Long00Leaf01059
import Proofs.RadenkovicGutmanD1Long00Leaf01060
import Proofs.RadenkovicGutmanD1Long00Leaf01061
import Proofs.RadenkovicGutmanD1Long00Leaf01062
import Proofs.RadenkovicGutmanD1Long00Leaf01063
import Proofs.RadenkovicGutmanD1Long00Leaf01064
import Proofs.RadenkovicGutmanD1Long00Leaf01065
import Proofs.RadenkovicGutmanD1Long00Leaf01066
import Proofs.RadenkovicGutmanD1Long00Leaf01067
import Proofs.RadenkovicGutmanD1Long00Leaf01068
import Proofs.RadenkovicGutmanD1Long00Leaf01069
import Proofs.RadenkovicGutmanD1Long00Leaf01070
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0062Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01054) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01055) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01056) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01057) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01058) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01059) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01060) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01061) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01062) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01063) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01064) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01065) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01066) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01067) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01068) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01069) (.leaf DegreeOneLongClass00.leaf01070))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/2),(9/16),(-164399497/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/2) (9/16) 0 1 0 1 (-164399497/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01054_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01055_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01056_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01057_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01058_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01059_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01060_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01061_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01062_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01063_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01064_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01065_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01066_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01067_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01068_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01069_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01070_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/16) : ℚ) : ℝ)-(((1/2) : ℚ) : ℝ))*(((-164399497/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/2) : ℚ) : ℝ)..(((9/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0062Complete
