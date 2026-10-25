/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00714
import Proofs.RadenkovicGutmanD1Long00Leaf00715
import Proofs.RadenkovicGutmanD1Long00Leaf00716
import Proofs.RadenkovicGutmanD1Long00Leaf00717
import Proofs.RadenkovicGutmanD1Long00Leaf00718
import Proofs.RadenkovicGutmanD1Long00Leaf00719
import Proofs.RadenkovicGutmanD1Long00Leaf00720
import Proofs.RadenkovicGutmanD1Long00Leaf00721
import Proofs.RadenkovicGutmanD1Long00Leaf00722
import Proofs.RadenkovicGutmanD1Long00Leaf00723
import Proofs.RadenkovicGutmanD1Long00Leaf00724
import Proofs.RadenkovicGutmanD1Long00Leaf00725
import Proofs.RadenkovicGutmanD1Long00Leaf00726
import Proofs.RadenkovicGutmanD1Long00Leaf00727
import Proofs.RadenkovicGutmanD1Long00Leaf00728
import Proofs.RadenkovicGutmanD1Long00Leaf00729
import Proofs.RadenkovicGutmanD1Long00Leaf00730
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0042Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00714) (.leaf DegreeOneLongClass00.leaf00715)) (.leaf DegreeOneLongClass00.leaf00716)) (.leaf DegreeOneLongClass00.leaf00717)) (.leaf DegreeOneLongClass00.leaf00718)) (.leaf DegreeOneLongClass00.leaf00719)) (.leaf DegreeOneLongClass00.leaf00720)) (.leaf DegreeOneLongClass00.leaf00721)) (.leaf DegreeOneLongClass00.leaf00722)) (.leaf DegreeOneLongClass00.leaf00723)) (.leaf DegreeOneLongClass00.leaf00724)) (.leaf DegreeOneLongClass00.leaf00725)) (.leaf DegreeOneLongClass00.leaf00726)) (.leaf DegreeOneLongClass00.leaf00727)) (.leaf DegreeOneLongClass00.leaf00728)) (.leaf DegreeOneLongClass00.leaf00729)) (.leaf DegreeOneLongClass00.leaf00730)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/160),(3/40),(-4860242791/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/160) (3/40) 0 1 0 1 (-4860242791/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00714_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00715_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00716_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00717_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00718_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00719_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00720_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00721_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00722_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00723_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00724_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00725_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00726_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00727_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00728_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00729_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00730_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/40) : ℚ) : ℝ)-(((11/160) : ℚ) : ℝ))*(((-4860242791/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/160) : ℚ) : ℝ)..(((3/40) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0042Complete
