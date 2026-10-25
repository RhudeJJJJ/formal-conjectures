/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4OriginalFallbackGroup0164Half0
import Proofs.RadenkovicGutmanD4OriginalFallbackGroup0164Half1
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D4OriginalFallbackGroup0164Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.leaf D4OriginalFallbackGroup0164.leaf00656) (.leaf D4OriginalFallbackGroup0164.leaf00657)) (.second (1/2) (.leaf D4OriginalFallbackGroup0164.leaf00658) (.leaf D4OriginalFallbackGroup0164.leaf00659))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(31/80),(17/40),(-109372390853048925699/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 4 4 4 (31/80) (17/40) 0 1 0 1 (-109372390853048925699/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨D4OriginalFallbackGroup0164.leaf00656_checked,by decide +kernel,by decide +kernel⟩,⟨D4OriginalFallbackGroup0164.leaf00657_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨D4OriginalFallbackGroup0164.leaf00658_checked,by decide +kernel,by decide +kernel⟩,⟨D4OriginalFallbackGroup0164.leaf00659_checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 4 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 4 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=4)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((17/40) : ℚ) : ℝ)-(((31/80) : ℚ) : ℝ))*(((-109372390853048925699/590295810358705651712) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((31/80) : ℚ) : ℝ)..(((17/40) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 4 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D4OriginalFallbackGroup0164Complete
