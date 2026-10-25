/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf00136
import Proofs.RadenkovicGutmanD1Long00Leaf00137
import Proofs.RadenkovicGutmanD1Long00Leaf00138
import Proofs.RadenkovicGutmanD1Long00Leaf00139
import Proofs.RadenkovicGutmanD1Long00Leaf00140
import Proofs.RadenkovicGutmanD1Long00Leaf00141
import Proofs.RadenkovicGutmanD1Long00Leaf00142
import Proofs.RadenkovicGutmanD1Long00Leaf00143
import Proofs.RadenkovicGutmanD1Long00Leaf00144
import Proofs.RadenkovicGutmanD1Long00Leaf00145
import Proofs.RadenkovicGutmanD1Long00Leaf00146
import Proofs.RadenkovicGutmanD1Long00Leaf00147
import Proofs.RadenkovicGutmanD1Long00Leaf00148
import Proofs.RadenkovicGutmanD1Long00Leaf00149
import Proofs.RadenkovicGutmanD1Long00Leaf00150
import Proofs.RadenkovicGutmanD1Long00Leaf00151
import Proofs.RadenkovicGutmanD1Long00Leaf00152
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0008Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.first (1/4) (.second (1/4) (.first (1/8) (.second (1/8) (.first (1/16) (.second (1/16) (.first (1/32) (.second (1/32) (.first (1/64) (.second (1/64) (.first (1/128) (.second (1/128) (.first (1/256) (.second (1/256) (.leaf DegreeOneLongClass00.leaf00136) (.leaf DegreeOneLongClass00.leaf00137)) (.leaf DegreeOneLongClass00.leaf00138)) (.leaf DegreeOneLongClass00.leaf00139)) (.leaf DegreeOneLongClass00.leaf00140)) (.leaf DegreeOneLongClass00.leaf00141)) (.leaf DegreeOneLongClass00.leaf00142)) (.leaf DegreeOneLongClass00.leaf00143)) (.leaf DegreeOneLongClass00.leaf00144)) (.leaf DegreeOneLongClass00.leaf00145)) (.leaf DegreeOneLongClass00.leaf00146)) (.leaf DegreeOneLongClass00.leaf00147)) (.leaf DegreeOneLongClass00.leaf00148)) (.leaf DegreeOneLongClass00.leaf00149)) (.leaf DegreeOneLongClass00.leaf00150)) (.leaf DegreeOneLongClass00.leaf00151)) (.leaf DegreeOneLongClass00.leaf00152)
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(41/16000),(11/4000),(-1170140969/268435456)⟩
theorem cover_checked : FastArmCover.accepts 1 4 4 (41/16000) (11/4000) 0 1 0 1 (-1170140969/268435456) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨DegreeOneLongClass00.leaf00136_checked,by decide +kernel,by decide +kernel⟩,⟨DegreeOneLongClass00.leaf00137_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00138_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00139_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00140_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00141_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00142_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00143_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00144_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00145_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00146_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00147_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00148_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00149_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00150_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00151_checked,by decide +kernel,by decide +kernel⟩⟩,⟨DegreeOneLongClass00.leaf00152_checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 1 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 1 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((11/4000) : ℚ) : ℝ)-(((41/16000) : ℚ) : ℝ))*(((-1170140969/268435456) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((41/16000) : ℚ) : ℝ)..(((11/4000) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 1 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D1OriginalSharedSlice0008Complete
