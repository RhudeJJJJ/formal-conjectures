/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00374
import Proofs.RadenkovicGutmanD1Long00Leaf00375
import Proofs.RadenkovicGutmanD1Long00Leaf00376
import Proofs.RadenkovicGutmanD1Long00Leaf00377
import Proofs.RadenkovicGutmanD1Long00Leaf00378
import Proofs.RadenkovicGutmanD1Long00Leaf00379
import Proofs.RadenkovicGutmanD1Long00Leaf00380
import Proofs.RadenkovicGutmanD1Long00Leaf00381
import Proofs.RadenkovicGutmanD1Long00Leaf00382
import Proofs.RadenkovicGutmanD1Long00Leaf00383
import Proofs.RadenkovicGutmanD1Long00Leaf00384
import Proofs.RadenkovicGutmanD1Long00Leaf00385
import Proofs.RadenkovicGutmanD1Long00Leaf00386
import Proofs.RadenkovicGutmanD1Long00Leaf00387
import Proofs.RadenkovicGutmanD1Long00Leaf00388
import Proofs.RadenkovicGutmanD1Long00Leaf00389
import Proofs.RadenkovicGutmanD1Long00Leaf00390
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0022Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00374) (.leaf DegreeOneLongClass00.leaf00375)) (.leaf DegreeOneLongClass00.leaf00376)) (.leaf DegreeOneLongClass00.leaf00377)) (.leaf DegreeOneLongClass00.leaf00378)) (.leaf DegreeOneLongClass00.leaf00379)) (.leaf DegreeOneLongClass00.leaf00380)) (.leaf DegreeOneLongClass00.leaf00381)) (.leaf DegreeOneLongClass00.leaf00382)) (.leaf DegreeOneLongClass00.leaf00383)) (.leaf DegreeOneLongClass00.leaf00384)) (.leaf DegreeOneLongClass00.leaf00385)) (.leaf DegreeOneLongClass00.leaf00386)) (.leaf DegreeOneLongClass00.leaf00387)) (.leaf DegreeOneLongClass00.leaf00388)) (.leaf DegreeOneLongClass00.leaf00389)) (.leaf DegreeOneLongClass00.leaf00390)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/800),(3/320),(-13445135859/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/800) (3/320) 0 1 0 1 (-13445135859/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00374_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00375_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00376_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00377_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00378_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00379_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00380_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00381_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00382_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00383_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00384_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00385_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00386_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00387_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00388_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00389_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00390_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/320) : ℚ) : ℝ)-(((7/800) : ℚ) : ℝ))*(((-13445135859/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/800) : ℚ) : ℝ)..(((3/320) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0022Complete
