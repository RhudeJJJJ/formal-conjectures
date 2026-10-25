/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00204
import Proofs.RadenkovicGutmanD1Long00Leaf00205
import Proofs.RadenkovicGutmanD1Long00Leaf00206
import Proofs.RadenkovicGutmanD1Long00Leaf00207
import Proofs.RadenkovicGutmanD1Long00Leaf00208
import Proofs.RadenkovicGutmanD1Long00Leaf00209
import Proofs.RadenkovicGutmanD1Long00Leaf00210
import Proofs.RadenkovicGutmanD1Long00Leaf00211
import Proofs.RadenkovicGutmanD1Long00Leaf00212
import Proofs.RadenkovicGutmanD1Long00Leaf00213
import Proofs.RadenkovicGutmanD1Long00Leaf00214
import Proofs.RadenkovicGutmanD1Long00Leaf00215
import Proofs.RadenkovicGutmanD1Long00Leaf00216
import Proofs.RadenkovicGutmanD1Long00Leaf00217
import Proofs.RadenkovicGutmanD1Long00Leaf00218
import Proofs.RadenkovicGutmanD1Long00Leaf00219
import Proofs.RadenkovicGutmanD1Long00Leaf00220
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0012Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00204) (.leaf DegreeOneLongClass00.leaf00205)) (.leaf DegreeOneLongClass00.leaf00206)) (.leaf DegreeOneLongClass00.leaf00207)) (.leaf DegreeOneLongClass00.leaf00208)) (.leaf DegreeOneLongClass00.leaf00209)) (.leaf DegreeOneLongClass00.leaf00210)) (.leaf DegreeOneLongClass00.leaf00211)) (.leaf DegreeOneLongClass00.leaf00212)) (.leaf DegreeOneLongClass00.leaf00213)) (.leaf DegreeOneLongClass00.leaf00214)) (.leaf DegreeOneLongClass00.leaf00215)) (.leaf DegreeOneLongClass00.leaf00216)) (.leaf DegreeOneLongClass00.leaf00217)) (.leaf DegreeOneLongClass00.leaf00218)) (.leaf DegreeOneLongClass00.leaf00219)) (.leaf DegreeOneLongClass00.leaf00220)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(31/8000),(17/4000),(-8470572547/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (31/8000) (17/4000) 0 1 0 1 (-8470572547/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00204_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00205_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00206_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00207_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00208_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00209_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00210_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00211_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00212_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00213_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00214_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00215_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00216_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00217_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00218_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00219_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00220_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/4000) : ℚ) : ℝ)-(((31/8000) : ℚ) : ℝ))*(((-8470572547/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((31/8000) : ℚ) : ℝ)..(((17/4000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0012Complete
