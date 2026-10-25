/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01122
import Proofs.RadenkovicGutmanD1Long00Leaf01123
import Proofs.RadenkovicGutmanD1Long00Leaf01124
import Proofs.RadenkovicGutmanD1Long00Leaf01125
import Proofs.RadenkovicGutmanD1Long00Leaf01126
import Proofs.RadenkovicGutmanD1Long00Leaf01127
import Proofs.RadenkovicGutmanD1Long00Leaf01128
import Proofs.RadenkovicGutmanD1Long00Leaf01129
import Proofs.RadenkovicGutmanD1Long00Leaf01130
import Proofs.RadenkovicGutmanD1Long00Leaf01131
import Proofs.RadenkovicGutmanD1Long00Leaf01132
import Proofs.RadenkovicGutmanD1Long00Leaf01133
import Proofs.RadenkovicGutmanD1Long00Leaf01134
import Proofs.RadenkovicGutmanD1Long00Leaf01135
import Proofs.RadenkovicGutmanD1Long00Leaf01136
import Proofs.RadenkovicGutmanD1Long00Leaf01137
import Proofs.RadenkovicGutmanD1Long00Leaf01138
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0066Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01122) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01123) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01124) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01125) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01126) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01127) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01128) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01129) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01130) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01131) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01132) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01133) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01134) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01135) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01136) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01137) (.leaf DegreeOneLongClass00.leaf01138))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(3/4),(13/16),(145334213/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (3/4) (13/16) 0 1 0 1 (145334213/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01122_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01123_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01124_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01125_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01126_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01127_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01128_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01129_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01130_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01131_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01132_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01133_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01134_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01135_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01136_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01137_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01138_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((13/16) : ℚ) : ℝ)-(((3/4) : ℚ) : ℝ))*(((145334213/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((3/4) : ℚ) : ℝ)..(((13/16) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0066Complete
