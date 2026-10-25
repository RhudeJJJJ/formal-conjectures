/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1176Part00
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1176Part01
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1176Part02
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1176Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.first (1/4) (.leaf D2OriginalFallbackGroup1176.leaf05888) (.leaf D2OriginalFallbackGroup1176.leaf05889)) (.first (3/4) (.second (1/2) (.leaf D2OriginalFallbackGroup1176.leaf05890) (.leaf D2OriginalFallbackGroup1176.leaf05891)) (.second (1/2) (.leaf D2OriginalFallbackGroup1176.leaf05892) (.leaf D2OriginalFallbackGroup1176.leaf05893)))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(37/80),(77/160),(-475723025752247811391/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (37/80) (77/160) 0 1 0 1 (-475723025752247811391/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨D2OriginalFallbackGroup1176.leaf05888_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1176.leaf05889_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨⟨D2OriginalFallbackGroup1176.leaf05890_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1176.leaf05891_checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨D2OriginalFallbackGroup1176.leaf05892_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1176.leaf05893_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=2)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((77/160) : ℚ) : ℝ)-(((37/80) : ℚ) : ℝ))*(((-475723025752247811391/4722366482869645213696) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((37/80) : ℚ) : ℝ)..(((77/160) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 2 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1176Complete
