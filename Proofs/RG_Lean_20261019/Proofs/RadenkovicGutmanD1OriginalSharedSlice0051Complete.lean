/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00867
import Proofs.RadenkovicGutmanD1Long00Leaf00868
import Proofs.RadenkovicGutmanD1Long00Leaf00869
import Proofs.RadenkovicGutmanD1Long00Leaf00870
import Proofs.RadenkovicGutmanD1Long00Leaf00871
import Proofs.RadenkovicGutmanD1Long00Leaf00872
import Proofs.RadenkovicGutmanD1Long00Leaf00873
import Proofs.RadenkovicGutmanD1Long00Leaf00874
import Proofs.RadenkovicGutmanD1Long00Leaf00875
import Proofs.RadenkovicGutmanD1Long00Leaf00876
import Proofs.RadenkovicGutmanD1Long00Leaf00877
import Proofs.RadenkovicGutmanD1Long00Leaf00878
import Proofs.RadenkovicGutmanD1Long00Leaf00879
import Proofs.RadenkovicGutmanD1Long00Leaf00880
import Proofs.RadenkovicGutmanD1Long00Leaf00881
import Proofs.RadenkovicGutmanD1Long00Leaf00882
import Proofs.RadenkovicGutmanD1Long00Leaf00883
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0051Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00867) (.leaf DegreeOneLongClass00.leaf00868)) (.leaf DegreeOneLongClass00.leaf00869)) (.leaf DegreeOneLongClass00.leaf00870)) (.leaf DegreeOneLongClass00.leaf00871)) (.leaf DegreeOneLongClass00.leaf00872)) (.leaf DegreeOneLongClass00.leaf00873)) (.leaf DegreeOneLongClass00.leaf00874)) (.leaf DegreeOneLongClass00.leaf00875)) (.leaf DegreeOneLongClass00.leaf00876)) (.leaf DegreeOneLongClass00.leaf00877)) (.leaf DegreeOneLongClass00.leaf00878)) (.leaf DegreeOneLongClass00.leaf00879)) (.leaf DegreeOneLongClass00.leaf00880)) (.leaf DegreeOneLongClass00.leaf00881)) (.leaf DegreeOneLongClass00.leaf00882)) (.leaf DegreeOneLongClass00.leaf00883)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/40),(1/5),(-1861520829/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (7/40) (1/5) 0 1 0 1 (-1861520829/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00867_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00868_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00869_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00870_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00871_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00872_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00873_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00874_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00875_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00876_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00877_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00878_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00879_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00880_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00881_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00882_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00883_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/5) : ℚ) : ℝ)-(((7/40) : ℚ) : ℝ))*(((-1861520829/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((7/40) : ℚ) : ℝ)..(((1/5) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0051Complete
