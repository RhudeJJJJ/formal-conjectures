/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00918
import Proofs.RadenkovicGutmanD1Long00Leaf00919
import Proofs.RadenkovicGutmanD1Long00Leaf00920
import Proofs.RadenkovicGutmanD1Long00Leaf00921
import Proofs.RadenkovicGutmanD1Long00Leaf00922
import Proofs.RadenkovicGutmanD1Long00Leaf00923
import Proofs.RadenkovicGutmanD1Long00Leaf00924
import Proofs.RadenkovicGutmanD1Long00Leaf00925
import Proofs.RadenkovicGutmanD1Long00Leaf00926
import Proofs.RadenkovicGutmanD1Long00Leaf00927
import Proofs.RadenkovicGutmanD1Long00Leaf00928
import Proofs.RadenkovicGutmanD1Long00Leaf00929
import Proofs.RadenkovicGutmanD1Long00Leaf00930
import Proofs.RadenkovicGutmanD1Long00Leaf00931
import Proofs.RadenkovicGutmanD1Long00Leaf00932
import Proofs.RadenkovicGutmanD1Long00Leaf00933
import Proofs.RadenkovicGutmanD1Long00Leaf00934
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0054Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00918) (.leaf DegreeOneLongClass00.leaf00919)) (.leaf DegreeOneLongClass00.leaf00920)) (.leaf DegreeOneLongClass00.leaf00921)) (.leaf DegreeOneLongClass00.leaf00922)) (.leaf DegreeOneLongClass00.leaf00923)) (.leaf DegreeOneLongClass00.leaf00924)) (.leaf DegreeOneLongClass00.leaf00925)) (.leaf DegreeOneLongClass00.leaf00926)) (.leaf DegreeOneLongClass00.leaf00927)) (.leaf DegreeOneLongClass00.leaf00928)) (.leaf DegreeOneLongClass00.leaf00929)) (.leaf DegreeOneLongClass00.leaf00930)) (.leaf DegreeOneLongClass00.leaf00931)) (.leaf DegreeOneLongClass00.leaf00932)) (.leaf DegreeOneLongClass00.leaf00933)) (.leaf DegreeOneLongClass00.leaf00934)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(19/80),(41/160),(-1189597429/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (19/80) (41/160) 0 1 0 1 (-1189597429/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00918_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00919_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00920_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00921_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00922_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00923_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00924_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00925_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00926_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00927_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00928_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00929_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00930_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00931_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00932_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00933_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00934_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((41/160) : ℚ) : ℝ)-(((19/80) : ℚ) : ℝ))*(((-1189597429/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((19/80) : ℚ) : ℝ)..(((41/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0054Complete
