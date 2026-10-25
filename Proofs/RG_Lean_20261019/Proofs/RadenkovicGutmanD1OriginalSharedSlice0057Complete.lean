/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00969
import Proofs.RadenkovicGutmanD1Long00Leaf00970
import Proofs.RadenkovicGutmanD1Long00Leaf00971
import Proofs.RadenkovicGutmanD1Long00Leaf00972
import Proofs.RadenkovicGutmanD1Long00Leaf00973
import Proofs.RadenkovicGutmanD1Long00Leaf00974
import Proofs.RadenkovicGutmanD1Long00Leaf00975
import Proofs.RadenkovicGutmanD1Long00Leaf00976
import Proofs.RadenkovicGutmanD1Long00Leaf00977
import Proofs.RadenkovicGutmanD1Long00Leaf00978
import Proofs.RadenkovicGutmanD1Long00Leaf00979
import Proofs.RadenkovicGutmanD1Long00Leaf00980
import Proofs.RadenkovicGutmanD1Long00Leaf00981
import Proofs.RadenkovicGutmanD1Long00Leaf00982
import Proofs.RadenkovicGutmanD1Long00Leaf00983
import Proofs.RadenkovicGutmanD1Long00Leaf00984
import Proofs.RadenkovicGutmanD1Long00Leaf00985
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0057Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00969) (.leaf DegreeOneLongClass00.leaf00970)) (.leaf DegreeOneLongClass00.leaf00971)) (.leaf DegreeOneLongClass00.leaf00972)) (.leaf DegreeOneLongClass00.leaf00973)) (.leaf DegreeOneLongClass00.leaf00974)) (.leaf DegreeOneLongClass00.leaf00975)) (.leaf DegreeOneLongClass00.leaf00976)) (.leaf DegreeOneLongClass00.leaf00977)) (.leaf DegreeOneLongClass00.leaf00978)) (.leaf DegreeOneLongClass00.leaf00979)) (.leaf DegreeOneLongClass00.leaf00980)) (.leaf DegreeOneLongClass00.leaf00981)) (.leaf DegreeOneLongClass00.leaf00982)) (.leaf DegreeOneLongClass00.leaf00983)) (.leaf DegreeOneLongClass00.leaf00984)) (.leaf DegreeOneLongClass00.leaf00985)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(5/16),(7/20),(-180528605/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (5/16) (7/20) 0 1 0 1 (-180528605/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00969_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00970_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00971_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00972_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00973_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00974_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00975_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00976_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00977_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00978_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00979_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00980_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00981_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00982_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00983_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00984_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00985_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/20) : ℚ) : ℝ)-(((5/16) : ℚ) : ℝ))*(((-180528605/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((5/16) : ℚ) : ℝ)..(((7/20) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0057Complete
