/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00306
import Proofs.RadenkovicGutmanD1Long00Leaf00307
import Proofs.RadenkovicGutmanD1Long00Leaf00308
import Proofs.RadenkovicGutmanD1Long00Leaf00309
import Proofs.RadenkovicGutmanD1Long00Leaf00310
import Proofs.RadenkovicGutmanD1Long00Leaf00311
import Proofs.RadenkovicGutmanD1Long00Leaf00312
import Proofs.RadenkovicGutmanD1Long00Leaf00313
import Proofs.RadenkovicGutmanD1Long00Leaf00314
import Proofs.RadenkovicGutmanD1Long00Leaf00315
import Proofs.RadenkovicGutmanD1Long00Leaf00316
import Proofs.RadenkovicGutmanD1Long00Leaf00317
import Proofs.RadenkovicGutmanD1Long00Leaf00318
import Proofs.RadenkovicGutmanD1Long00Leaf00319
import Proofs.RadenkovicGutmanD1Long00Leaf00320
import Proofs.RadenkovicGutmanD1Long00Leaf00321
import Proofs.RadenkovicGutmanD1Long00Leaf00322
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0018Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00306) (.leaf DegreeOneLongClass00.leaf00307)) (.leaf DegreeOneLongClass00.leaf00308)) (.leaf DegreeOneLongClass00.leaf00309)) (.leaf DegreeOneLongClass00.leaf00310)) (.leaf DegreeOneLongClass00.leaf00311)) (.leaf DegreeOneLongClass00.leaf00312)) (.leaf DegreeOneLongClass00.leaf00313)) (.leaf DegreeOneLongClass00.leaf00314)) (.leaf DegreeOneLongClass00.leaf00315)) (.leaf DegreeOneLongClass00.leaf00316)) (.leaf DegreeOneLongClass00.leaf00317)) (.leaf DegreeOneLongClass00.leaf00318)) (.leaf DegreeOneLongClass00.leaf00319)) (.leaf DegreeOneLongClass00.leaf00320)) (.leaf DegreeOneLongClass00.leaf00321)) (.leaf DegreeOneLongClass00.leaf00322)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/160),(11/1600),(-7444074387/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/160) (11/1600) 0 1 0 1 (-7444074387/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00306_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00307_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00308_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00309_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00310_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00311_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00312_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00313_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00314_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00315_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00316_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00317_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00318_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00319_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00320_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00321_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00322_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/1600) : ℚ) : ℝ)-(((1/160) : ℚ) : ℝ))*(((-7444074387/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/160) : ℚ) : ℝ)..(((11/1600) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0018Complete
