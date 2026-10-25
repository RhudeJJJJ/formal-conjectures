/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00000
import Proofs.RadenkovicGutmanD1Long00Leaf00001
import Proofs.RadenkovicGutmanD1Long00Leaf00002
import Proofs.RadenkovicGutmanD1Long00Leaf00003
import Proofs.RadenkovicGutmanD1Long00Leaf00004
import Proofs.RadenkovicGutmanD1Long00Leaf00005
import Proofs.RadenkovicGutmanD1Long00Leaf00006
import Proofs.RadenkovicGutmanD1Long00Leaf00007
import Proofs.RadenkovicGutmanD1Long00Leaf00008
import Proofs.RadenkovicGutmanD1Long00Leaf00009
import Proofs.RadenkovicGutmanD1Long00Leaf00010
import Proofs.RadenkovicGutmanD1Long00Leaf00011
import Proofs.RadenkovicGutmanD1Long00Leaf00012
import Proofs.RadenkovicGutmanD1Long00Leaf00013
import Proofs.RadenkovicGutmanD1Long00Leaf00014
import Proofs.RadenkovicGutmanD1Long00Leaf00015
import Proofs.RadenkovicGutmanD1Long00Leaf00016
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0000Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00000) (.leaf DegreeOneLongClass00.leaf00001)) (.leaf DegreeOneLongClass00.leaf00002)) (.leaf DegreeOneLongClass00.leaf00003)) (.leaf DegreeOneLongClass00.leaf00004)) (.leaf DegreeOneLongClass00.leaf00005)) (.leaf DegreeOneLongClass00.leaf00006)) (.leaf DegreeOneLongClass00.leaf00007)) (.leaf DegreeOneLongClass00.leaf00008)) (.leaf DegreeOneLongClass00.leaf00009)) (.leaf DegreeOneLongClass00.leaf00010)) (.leaf DegreeOneLongClass00.leaf00011)) (.leaf DegreeOneLongClass00.leaf00012)) (.leaf DegreeOneLongClass00.leaf00013)) (.leaf DegreeOneLongClass00.leaf00014)) (.leaf DegreeOneLongClass00.leaf00015)) (.leaf DegreeOneLongClass00.leaf00016)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/1000),(9/8000),(-22870244509/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (1/1000) (9/8000) 0 1 0 1 (-22870244509/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00000_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00001_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00002_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00003_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00004_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00005_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00006_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00007_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00008_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00009_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00010_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00011_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00012_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00013_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00014_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00015_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00016_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((9/8000) : ℚ) : ℝ)-(((1/1000) : ℚ) : ℝ))*(((-22870244509/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((1/1000) : ℚ) : ℝ)..(((9/8000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0000Complete
