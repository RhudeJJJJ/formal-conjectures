/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00782
import Proofs.RadenkovicGutmanD1Long00Leaf00783
import Proofs.RadenkovicGutmanD1Long00Leaf00784
import Proofs.RadenkovicGutmanD1Long00Leaf00785
import Proofs.RadenkovicGutmanD1Long00Leaf00786
import Proofs.RadenkovicGutmanD1Long00Leaf00787
import Proofs.RadenkovicGutmanD1Long00Leaf00788
import Proofs.RadenkovicGutmanD1Long00Leaf00789
import Proofs.RadenkovicGutmanD1Long00Leaf00790
import Proofs.RadenkovicGutmanD1Long00Leaf00791
import Proofs.RadenkovicGutmanD1Long00Leaf00792
import Proofs.RadenkovicGutmanD1Long00Leaf00793
import Proofs.RadenkovicGutmanD1Long00Leaf00794
import Proofs.RadenkovicGutmanD1Long00Leaf00795
import Proofs.RadenkovicGutmanD1Long00Leaf00796
import Proofs.RadenkovicGutmanD1Long00Leaf00797
import Proofs.RadenkovicGutmanD1Long00Leaf00798
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0046Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00782) (.leaf DegreeOneLongClass00.leaf00783)) (.leaf DegreeOneLongClass00.leaf00784)) (.leaf DegreeOneLongClass00.leaf00785)) (.leaf DegreeOneLongClass00.leaf00786)) (.leaf DegreeOneLongClass00.leaf00787)) (.leaf DegreeOneLongClass00.leaf00788)) (.leaf DegreeOneLongClass00.leaf00789)) (.leaf DegreeOneLongClass00.leaf00790)) (.leaf DegreeOneLongClass00.leaf00791)) (.leaf DegreeOneLongClass00.leaf00792)) (.leaf DegreeOneLongClass00.leaf00793)) (.leaf DegreeOneLongClass00.leaf00794)) (.leaf DegreeOneLongClass00.leaf00795)) (.leaf DegreeOneLongClass00.leaf00796)) (.leaf DegreeOneLongClass00.leaf00797)) (.leaf DegreeOneLongClass00.leaf00798)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(9/80),(1/8),(-3122388125/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (9/80) (1/8) 0 1 0 1 (-3122388125/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00782_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00783_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00784_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00785_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00786_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00787_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00788_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00789_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00790_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00791_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00792_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00793_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00794_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00795_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00796_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00797_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00798_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((1/8) : ℚ) : ℝ)-(((9/80) : ℚ) : ℝ))*(((-3122388125/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((9/80) : ℚ) : ℝ)..(((1/8) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0046Complete
