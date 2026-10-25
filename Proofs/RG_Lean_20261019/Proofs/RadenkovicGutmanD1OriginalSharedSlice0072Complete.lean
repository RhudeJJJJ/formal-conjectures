/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01224
import Proofs.RadenkovicGutmanD1Long00Leaf01225
import Proofs.RadenkovicGutmanD1Long00Leaf01226
import Proofs.RadenkovicGutmanD1Long00Leaf01227
import Proofs.RadenkovicGutmanD1Long00Leaf01228
import Proofs.RadenkovicGutmanD1Long00Leaf01229
import Proofs.RadenkovicGutmanD1Long00Leaf01230
import Proofs.RadenkovicGutmanD1Long00Leaf01231
import Proofs.RadenkovicGutmanD1Long00Leaf01232
import Proofs.RadenkovicGutmanD1Long00Leaf01233
import Proofs.RadenkovicGutmanD1Long00Leaf01234
import Proofs.RadenkovicGutmanD1Long00Leaf01235
import Proofs.RadenkovicGutmanD1Long00Leaf01236
import Proofs.RadenkovicGutmanD1Long00Leaf01237
import Proofs.RadenkovicGutmanD1Long00Leaf01238
import Proofs.RadenkovicGutmanD1Long00Leaf01239
import Proofs.RadenkovicGutmanD1Long00Leaf01240
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0072Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01224) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01225) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01226) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01227) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01228) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01229) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01230) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01231) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01232) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01233) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01234) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01235) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01236) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01237) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01238) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01239) (.leaf DegreeOneLongClass00.leaf01240))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(4/3),(8/5),(47601133/536870912)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (4/3) (8/5) 0 1 0 1 (47601133/536870912) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01224_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01225_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01226_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01227_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01228_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01229_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01230_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01231_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01232_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01233_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01234_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01235_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01236_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01237_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01238_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01239_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01240_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((8/5) : ℚ) : ℝ)-(((4/3) : ℚ) : ℝ))*(((47601133/536870912) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((4/3) : ℚ) : ℝ)..(((8/5) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0072Complete
