/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3OriginalFallbackGroup0806Half0
import Proofs.RadenkovicGutmanD3OriginalFallbackGroup0806Half1
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D3OriginalFallbackGroup0806Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.second (1/2) (.leaf D3OriginalFallbackGroup0806.leaf03224) (.leaf D3OriginalFallbackGroup0806.leaf03225)) (.second (1/2) (.leaf D3OriginalFallbackGroup0806.leaf03226) (.leaf D3OriginalFallbackGroup0806.leaf03227))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(17/40),(37/80),(-702802337294365329211/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 3 4 4 (17/40) (37/80) 0 1 0 1 (-702802337294365329211/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨D3OriginalFallbackGroup0806.leaf03224_checked,by decide +kernel,by decide +kernel⟩,⟨D3OriginalFallbackGroup0806.leaf03225_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨D3OriginalFallbackGroup0806.leaf03226_checked,by decide +kernel,by decide +kernel⟩,⟨D3OriginalFallbackGroup0806.leaf03227_checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=3)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((37/80) : ℚ) : ℝ)-(((17/40) : ℚ) : ℝ))*(((-702802337294365329211/4722366482869645213696) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((17/40) : ℚ) : ℝ)..(((37/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 3 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D3OriginalFallbackGroup0806Complete
