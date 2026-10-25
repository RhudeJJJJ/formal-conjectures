/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00289
import Proofs.RadenkovicGutmanD1Long00Leaf00290
import Proofs.RadenkovicGutmanD1Long00Leaf00291
import Proofs.RadenkovicGutmanD1Long00Leaf00292
import Proofs.RadenkovicGutmanD1Long00Leaf00293
import Proofs.RadenkovicGutmanD1Long00Leaf00294
import Proofs.RadenkovicGutmanD1Long00Leaf00295
import Proofs.RadenkovicGutmanD1Long00Leaf00296
import Proofs.RadenkovicGutmanD1Long00Leaf00297
import Proofs.RadenkovicGutmanD1Long00Leaf00298
import Proofs.RadenkovicGutmanD1Long00Leaf00299
import Proofs.RadenkovicGutmanD1Long00Leaf00300
import Proofs.RadenkovicGutmanD1Long00Leaf00301
import Proofs.RadenkovicGutmanD1Long00Leaf00302
import Proofs.RadenkovicGutmanD1Long00Leaf00303
import Proofs.RadenkovicGutmanD1Long00Leaf00304
import Proofs.RadenkovicGutmanD1Long00Leaf00305
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0017Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00289) (.leaf DegreeOneLongClass00.leaf00290)) (.leaf DegreeOneLongClass00.leaf00291)) (.leaf DegreeOneLongClass00.leaf00292)) (.leaf DegreeOneLongClass00.leaf00293)) (.leaf DegreeOneLongClass00.leaf00294)) (.leaf DegreeOneLongClass00.leaf00295)) (.leaf DegreeOneLongClass00.leaf00296)) (.leaf DegreeOneLongClass00.leaf00297)) (.leaf DegreeOneLongClass00.leaf00298)) (.leaf DegreeOneLongClass00.leaf00299)) (.leaf DegreeOneLongClass00.leaf00300)) (.leaf DegreeOneLongClass00.leaf00301)) (.leaf DegreeOneLongClass00.leaf00302)) (.leaf DegreeOneLongClass00.leaf00303)) (.leaf DegreeOneLongClass00.leaf00304)) (.leaf DegreeOneLongClass00.leaf00305)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/1600),(1/160),(-7670169285/2147483648)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/1600) (1/160) 0 1 0 1 (-7670169285/2147483648) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00289_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00290_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00291_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00292_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00293_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00294_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00295_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00296_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00297_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00298_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00299_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00300_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00301_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00302_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00303_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00304_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00305_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/160) : ℚ) : ℝ)-(((9/1600) : ℚ) : ℝ))*(((-7670169285/2147483648) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/1600) : ℚ) : ℝ)..(((1/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0017Complete
