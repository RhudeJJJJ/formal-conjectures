/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1174Part00
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1174Part01
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1174Part02
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1174Part03
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1174Part04
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1174Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.first (1/4) (.second (1/2) (.second (1/4) (.leaf D2OriginalFallbackGroup1174.leaf05871) (.leaf D2OriginalFallbackGroup1174.leaf05872)) (.leaf D2OriginalFallbackGroup1174.leaf05873)) (.second (1/2) (.second (1/4) (.leaf D2OriginalFallbackGroup1174.leaf05874) (.leaf D2OriginalFallbackGroup1174.leaf05875)) (.leaf D2OriginalFallbackGroup1174.leaf05876))) (.first (3/4) (.second (1/2) (.leaf D2OriginalFallbackGroup1174.leaf05877) (.leaf D2OriginalFallbackGroup1174.leaf05878)) (.leaf D2OriginalFallbackGroup1174.leaf05879))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/40),(71/160),(-565902447950372231887/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (17/40) (71/160) 0 1 0 1 (-565902447950372231887/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨D2OriginalFallbackGroup1174.leaf05871_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1174.leaf05872_checked,by decide +kernel,by decide +kernel⟩⟩,⟨D2OriginalFallbackGroup1174.leaf05873_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨⟨D2OriginalFallbackGroup1174.leaf05874_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1174.leaf05875_checked,by decide +kernel,by decide +kernel⟩⟩,⟨D2OriginalFallbackGroup1174.leaf05876_checked,by decide +kernel,by decide +kernel⟩⟩⟩,⟨⟨⟨D2OriginalFallbackGroup1174.leaf05877_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1174.leaf05878_checked,by decide +kernel,by decide +kernel⟩⟩,⟨D2OriginalFallbackGroup1174.leaf05879_checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=2)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((71/160) : ℚ) : ℝ)-(((17/40) : ℚ) : ℝ))*(((-565902447950372231887/4722366482869645213696) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/40) : ℚ) : ℝ)..(((71/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 2 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1174Complete
