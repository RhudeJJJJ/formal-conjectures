/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00323
import Proofs.RadenkovicGutmanD1Long00Leaf00324
import Proofs.RadenkovicGutmanD1Long00Leaf00325
import Proofs.RadenkovicGutmanD1Long00Leaf00326
import Proofs.RadenkovicGutmanD1Long00Leaf00327
import Proofs.RadenkovicGutmanD1Long00Leaf00328
import Proofs.RadenkovicGutmanD1Long00Leaf00329
import Proofs.RadenkovicGutmanD1Long00Leaf00330
import Proofs.RadenkovicGutmanD1Long00Leaf00331
import Proofs.RadenkovicGutmanD1Long00Leaf00332
import Proofs.RadenkovicGutmanD1Long00Leaf00333
import Proofs.RadenkovicGutmanD1Long00Leaf00334
import Proofs.RadenkovicGutmanD1Long00Leaf00335
import Proofs.RadenkovicGutmanD1Long00Leaf00336
import Proofs.RadenkovicGutmanD1Long00Leaf00337
import Proofs.RadenkovicGutmanD1Long00Leaf00338
import Proofs.RadenkovicGutmanD1Long00Leaf00339
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0019Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00323) (.leaf DegreeOneLongClass00.leaf00324)) (.leaf DegreeOneLongClass00.leaf00325)) (.leaf DegreeOneLongClass00.leaf00326)) (.leaf DegreeOneLongClass00.leaf00327)) (.leaf DegreeOneLongClass00.leaf00328)) (.leaf DegreeOneLongClass00.leaf00329)) (.leaf DegreeOneLongClass00.leaf00330)) (.leaf DegreeOneLongClass00.leaf00331)) (.leaf DegreeOneLongClass00.leaf00332)) (.leaf DegreeOneLongClass00.leaf00333)) (.leaf DegreeOneLongClass00.leaf00334)) (.leaf DegreeOneLongClass00.leaf00335)) (.leaf DegreeOneLongClass00.leaf00336)) (.leaf DegreeOneLongClass00.leaf00337)) (.leaf DegreeOneLongClass00.leaf00338)) (.leaf DegreeOneLongClass00.leaf00339)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/1600),(3/400),(-14479219039/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/1600) (3/400) 0 1 0 1 (-14479219039/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00323_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00324_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00325_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00326_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00327_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00328_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00329_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00330_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00331_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00332_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00333_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00334_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00335_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00336_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00337_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00338_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00339_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/400) : ℚ) : ℝ)-(((11/1600) : ℚ) : ℝ))*(((-14479219039/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/1600) : ℚ) : ℝ)..(((3/400) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0019Complete
