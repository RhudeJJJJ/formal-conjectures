/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00340
import Proofs.RadenkovicGutmanD1Long00Leaf00341
import Proofs.RadenkovicGutmanD1Long00Leaf00342
import Proofs.RadenkovicGutmanD1Long00Leaf00343
import Proofs.RadenkovicGutmanD1Long00Leaf00344
import Proofs.RadenkovicGutmanD1Long00Leaf00345
import Proofs.RadenkovicGutmanD1Long00Leaf00346
import Proofs.RadenkovicGutmanD1Long00Leaf00347
import Proofs.RadenkovicGutmanD1Long00Leaf00348
import Proofs.RadenkovicGutmanD1Long00Leaf00349
import Proofs.RadenkovicGutmanD1Long00Leaf00350
import Proofs.RadenkovicGutmanD1Long00Leaf00351
import Proofs.RadenkovicGutmanD1Long00Leaf00352
import Proofs.RadenkovicGutmanD1Long00Leaf00353
import Proofs.RadenkovicGutmanD1Long00Leaf00354
import Proofs.RadenkovicGutmanD1Long00Leaf00355
import Proofs.RadenkovicGutmanD1Long00Leaf00356
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0020Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00340) (.leaf DegreeOneLongClass00.leaf00341)) (.leaf DegreeOneLongClass00.leaf00342)) (.leaf DegreeOneLongClass00.leaf00343)) (.leaf DegreeOneLongClass00.leaf00344)) (.leaf DegreeOneLongClass00.leaf00345)) (.leaf DegreeOneLongClass00.leaf00346)) (.leaf DegreeOneLongClass00.leaf00347)) (.leaf DegreeOneLongClass00.leaf00348)) (.leaf DegreeOneLongClass00.leaf00349)) (.leaf DegreeOneLongClass00.leaf00350)) (.leaf DegreeOneLongClass00.leaf00351)) (.leaf DegreeOneLongClass00.leaf00352)) (.leaf DegreeOneLongClass00.leaf00353)) (.leaf DegreeOneLongClass00.leaf00354)) (.leaf DegreeOneLongClass00.leaf00355)) (.leaf DegreeOneLongClass00.leaf00356)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/400),(13/1600),(-14106009845/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/400) (13/1600) 0 1 0 1 (-14106009845/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00340_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00341_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00342_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00343_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00344_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00345_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00346_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00347_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00348_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00349_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00350_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00351_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00352_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00353_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00354_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00355_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00356_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((13/1600) : ℚ) : ℝ)-(((3/400) : ℚ) : ℝ))*(((-14106009845/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/400) : ℚ) : ℝ)..(((13/1600) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0020Complete
