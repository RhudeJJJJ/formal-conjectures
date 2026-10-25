/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01207
import Proofs.RadenkovicGutmanD1Long00Leaf01208
import Proofs.RadenkovicGutmanD1Long00Leaf01209
import Proofs.RadenkovicGutmanD1Long00Leaf01210
import Proofs.RadenkovicGutmanD1Long00Leaf01211
import Proofs.RadenkovicGutmanD1Long00Leaf01212
import Proofs.RadenkovicGutmanD1Long00Leaf01213
import Proofs.RadenkovicGutmanD1Long00Leaf01214
import Proofs.RadenkovicGutmanD1Long00Leaf01215
import Proofs.RadenkovicGutmanD1Long00Leaf01216
import Proofs.RadenkovicGutmanD1Long00Leaf01217
import Proofs.RadenkovicGutmanD1Long00Leaf01218
import Proofs.RadenkovicGutmanD1Long00Leaf01219
import Proofs.RadenkovicGutmanD1Long00Leaf01220
import Proofs.RadenkovicGutmanD1Long00Leaf01221
import Proofs.RadenkovicGutmanD1Long00Leaf01222
import Proofs.RadenkovicGutmanD1Long00Leaf01223
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0071Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.leaf DegreeOneLongClass00.leaf01207) (.second (1/2) (.leaf DegreeOneLongClass00.leaf01208) (.first (3/4) (.leaf DegreeOneLongClass00.leaf01209) (.second (3/4) (.leaf DegreeOneLongClass00.leaf01210) (.first (7/8) (.leaf DegreeOneLongClass00.leaf01211) (.second (7/8) (.leaf DegreeOneLongClass00.leaf01212) (.first (15/16) (.leaf DegreeOneLongClass00.leaf01213) (.second (15/16) (.leaf DegreeOneLongClass00.leaf01214) (.first (31/32) (.leaf DegreeOneLongClass00.leaf01215) (.second (31/32) (.leaf DegreeOneLongClass00.leaf01216) (.first (63/64) (.leaf DegreeOneLongClass00.leaf01217) (.second (63/64) (.leaf DegreeOneLongClass00.leaf01218) (.first (127/128) (.leaf DegreeOneLongClass00.leaf01219) (.second (127/128) (.leaf DegreeOneLongClass00.leaf01220) (.first (255/256) (.leaf DegreeOneLongClass00.leaf01221) (.second (255/256) (.leaf DegreeOneLongClass00.leaf01222) (.leaf DegreeOneLongClass00.leaf01223))))))))))))))))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(8/7),(4/3),(87362465/1073741824)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (8/7) (4/3) 0 1 0 1 (87362465/1073741824) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨DegreeOneLongClass00.leaf01207_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01208_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01209_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01210_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01211_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01212_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01213_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01214_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01215_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01216_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01217_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01218_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01219_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01220_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01221_checked,by decide +kernel,by decide +kernel⟩,⟨⟨DegreeOneLongClass00.leaf01222_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf01223_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((4/3) : ℚ) : ℝ)-(((8/7) : ℚ) : ℝ))*(((87362465/1073741824) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((8/7) : ℚ) : ℝ)..(((4/3) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0071Complete
