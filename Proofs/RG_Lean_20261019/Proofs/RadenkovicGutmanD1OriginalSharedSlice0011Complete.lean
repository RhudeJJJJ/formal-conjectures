/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00187
import Proofs.RadenkovicGutmanD1Long00Leaf00188
import Proofs.RadenkovicGutmanD1Long00Leaf00189
import Proofs.RadenkovicGutmanD1Long00Leaf00190
import Proofs.RadenkovicGutmanD1Long00Leaf00191
import Proofs.RadenkovicGutmanD1Long00Leaf00192
import Proofs.RadenkovicGutmanD1Long00Leaf00193
import Proofs.RadenkovicGutmanD1Long00Leaf00194
import Proofs.RadenkovicGutmanD1Long00Leaf00195
import Proofs.RadenkovicGutmanD1Long00Leaf00196
import Proofs.RadenkovicGutmanD1Long00Leaf00197
import Proofs.RadenkovicGutmanD1Long00Leaf00198
import Proofs.RadenkovicGutmanD1Long00Leaf00199
import Proofs.RadenkovicGutmanD1Long00Leaf00200
import Proofs.RadenkovicGutmanD1Long00Leaf00201
import Proofs.RadenkovicGutmanD1Long00Leaf00202
import Proofs.RadenkovicGutmanD1Long00Leaf00203
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0011Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00187) (.leaf DegreeOneLongClass00.leaf00188)) (.leaf DegreeOneLongClass00.leaf00189)) (.leaf DegreeOneLongClass00.leaf00190)) (.leaf DegreeOneLongClass00.leaf00191)) (.leaf DegreeOneLongClass00.leaf00192)) (.leaf DegreeOneLongClass00.leaf00193)) (.leaf DegreeOneLongClass00.leaf00194)) (.leaf DegreeOneLongClass00.leaf00195)) (.leaf DegreeOneLongClass00.leaf00196)) (.leaf DegreeOneLongClass00.leaf00197)) (.leaf DegreeOneLongClass00.leaf00198)) (.leaf DegreeOneLongClass00.leaf00199)) (.leaf DegreeOneLongClass00.leaf00200)) (.leaf DegreeOneLongClass00.leaf00201)) (.leaf DegreeOneLongClass00.leaf00202)) (.leaf DegreeOneLongClass00.leaf00203)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/2000),(31/8000),(-2172347521/536870912)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/2000) (31/8000) 0 1 0 1 (-2172347521/536870912) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00187_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00188_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00189_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00190_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00191_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00192_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00193_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00194_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00195_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00196_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00197_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00198_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00199_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00200_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00201_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00202_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00203_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((31/8000) : ℚ) : ℝ)-(((7/2000) : ℚ) : ℝ))*(((-2172347521/536870912) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/2000) : ℚ) : ℝ)..(((31/8000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0011Complete
