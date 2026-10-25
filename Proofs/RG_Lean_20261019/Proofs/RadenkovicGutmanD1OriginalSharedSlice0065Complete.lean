/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01105
import Proofs.RadenkovicGutmanD1Long00Leaf01106
import Proofs.RadenkovicGutmanD1Long00Leaf01107
import Proofs.RadenkovicGutmanD1Long00Leaf01108
import Proofs.RadenkovicGutmanD1Long00Leaf01109
import Proofs.RadenkovicGutmanD1Long00Leaf01110
import Proofs.RadenkovicGutmanD1Long00Leaf01111
import Proofs.RadenkovicGutmanD1Long00Leaf01112
import Proofs.RadenkovicGutmanD1Long00Leaf01113
import Proofs.RadenkovicGutmanD1Long00Leaf01114
import Proofs.RadenkovicGutmanD1Long00Leaf01115
import Proofs.RadenkovicGutmanD1Long00Leaf01116
import Proofs.RadenkovicGutmanD1Long00Leaf01117
import Proofs.RadenkovicGutmanD1Long00Leaf01118
import Proofs.RadenkovicGutmanD1Long00Leaf01119
import Proofs.RadenkovicGutmanD1Long00Leaf01120
import Proofs.RadenkovicGutmanD1Long00Leaf01121
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0065Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01105) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01106) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01107) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01108) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01109) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01110) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01111) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01112) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01113) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01114) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01115) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01116) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01117) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01118) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01119) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01120) (.leaf DegreeOneLongClass00.leaf01121))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/16),(3/4),(21133151/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (11/16) (3/4) 0 1 0 1 (21133151/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01105_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01106_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01107_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01108_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01109_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01110_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01111_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01112_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01113_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01114_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01115_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01116_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01117_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01118_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01119_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01120_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01121_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((3/4) : ℚ) : ℝ)-(((11/16) : ℚ) : ℝ))*(((21133151/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((11/16) : ℚ) : ℝ)..(((3/4) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0065Complete
