/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00935
import Proofs.RadenkovicGutmanD1Long00Leaf00936
import Proofs.RadenkovicGutmanD1Long00Leaf00937
import Proofs.RadenkovicGutmanD1Long00Leaf00938
import Proofs.RadenkovicGutmanD1Long00Leaf00939
import Proofs.RadenkovicGutmanD1Long00Leaf00940
import Proofs.RadenkovicGutmanD1Long00Leaf00941
import Proofs.RadenkovicGutmanD1Long00Leaf00942
import Proofs.RadenkovicGutmanD1Long00Leaf00943
import Proofs.RadenkovicGutmanD1Long00Leaf00944
import Proofs.RadenkovicGutmanD1Long00Leaf00945
import Proofs.RadenkovicGutmanD1Long00Leaf00946
import Proofs.RadenkovicGutmanD1Long00Leaf00947
import Proofs.RadenkovicGutmanD1Long00Leaf00948
import Proofs.RadenkovicGutmanD1Long00Leaf00949
import Proofs.RadenkovicGutmanD1Long00Leaf00950
import Proofs.RadenkovicGutmanD1Long00Leaf00951
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0055Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00935) (.leaf DegreeOneLongClass00.leaf00936)) (.leaf DegreeOneLongClass00.leaf00937)) (.leaf DegreeOneLongClass00.leaf00938)) (.leaf DegreeOneLongClass00.leaf00939)) (.leaf DegreeOneLongClass00.leaf00940)) (.leaf DegreeOneLongClass00.leaf00941)) (.leaf DegreeOneLongClass00.leaf00942)) (.leaf DegreeOneLongClass00.leaf00943)) (.leaf DegreeOneLongClass00.leaf00944)) (.leaf DegreeOneLongClass00.leaf00945)) (.leaf DegreeOneLongClass00.leaf00946)) (.leaf DegreeOneLongClass00.leaf00947)) (.leaf DegreeOneLongClass00.leaf00948)) (.leaf DegreeOneLongClass00.leaf00949)) (.leaf DegreeOneLongClass00.leaf00950)) (.leaf DegreeOneLongClass00.leaf00951)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(41/160),(11/40),(-1047843981/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (41/160) (11/40) 0 1 0 1 (-1047843981/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00935_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00936_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00937_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00938_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00939_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00940_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00941_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00942_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00943_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00944_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00945_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00946_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00947_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00948_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00949_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00950_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00951_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/40) : ℚ) : ℝ)-(((41/160) : ℚ) : ℝ))*(((-1047843981/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((41/160) : ℚ) : ℝ)..(((11/40) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0055Complete
