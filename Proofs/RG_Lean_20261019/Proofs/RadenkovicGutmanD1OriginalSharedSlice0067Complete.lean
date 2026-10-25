/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01139
import Proofs.RadenkovicGutmanD1Long00Leaf01140
import Proofs.RadenkovicGutmanD1Long00Leaf01141
import Proofs.RadenkovicGutmanD1Long00Leaf01142
import Proofs.RadenkovicGutmanD1Long00Leaf01143
import Proofs.RadenkovicGutmanD1Long00Leaf01144
import Proofs.RadenkovicGutmanD1Long00Leaf01145
import Proofs.RadenkovicGutmanD1Long00Leaf01146
import Proofs.RadenkovicGutmanD1Long00Leaf01147
import Proofs.RadenkovicGutmanD1Long00Leaf01148
import Proofs.RadenkovicGutmanD1Long00Leaf01149
import Proofs.RadenkovicGutmanD1Long00Leaf01150
import Proofs.RadenkovicGutmanD1Long00Leaf01151
import Proofs.RadenkovicGutmanD1Long00Leaf01152
import Proofs.RadenkovicGutmanD1Long00Leaf01153
import Proofs.RadenkovicGutmanD1Long00Leaf01154
import Proofs.RadenkovicGutmanD1Long00Leaf01155
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0067Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01139) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01140) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01141) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01142) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01143) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01144) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01145) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01146) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01147) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01148) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01149) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01150) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01151) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01152) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01153) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01154) (.leaf DegreeOneLongClass00.leaf01155))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(13/16),(7/8),(196554469/4294967296)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (13/16) (7/8) 0 1 0 1 (196554469/4294967296) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01139_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01140_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01141_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01142_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01143_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01144_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01145_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01146_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01147_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01148_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01149_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01150_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01151_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01152_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01153_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01154_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01155_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((7/8) : ℚ) : ℝ)-(((13/16) : ℚ) : ℝ))*(((196554469/4294967296) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((13/16) : ℚ) : ℝ)..(((7/8) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0067Complete
