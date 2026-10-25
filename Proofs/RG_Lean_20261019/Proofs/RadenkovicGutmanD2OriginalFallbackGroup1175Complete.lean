/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1175Part00
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1175Part01
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1175Part02
import Proofs.RadenkovicGutmanD2OriginalFallbackGroup1175Part03
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1175Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .first (1/2) (.first (1/4) (.leaf D2OriginalFallbackGroup1175.leaf05880) (.second (1/2) (.leaf D2OriginalFallbackGroup1175.leaf05881) (.second (3/4) (.leaf D2OriginalFallbackGroup1175.leaf05882) (.leaf D2OriginalFallbackGroup1175.leaf05883)))) (.first (3/4) (.second (1/2) (.leaf D2OriginalFallbackGroup1175.leaf05884) (.second (3/4) (.leaf D2OriginalFallbackGroup1175.leaf05885) (.leaf D2OriginalFallbackGroup1175.leaf05886))) (.leaf D2OriginalFallbackGroup1175.leaf05887))
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(71/160),(37/80),(-64733087483093856127/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (71/160) (37/80) 0 1 0 1 (-64733087483093856127/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨D2OriginalFallbackGroup1175.leaf05880_checked,by decide +kernel,by decide +kernel⟩,⟨⟨D2OriginalFallbackGroup1175.leaf05881_checked,by decide +kernel,by decide +kernel⟩,⟨⟨D2OriginalFallbackGroup1175.leaf05882_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1175.leaf05883_checked,by decide +kernel,by decide +kernel⟩⟩⟩⟩,⟨⟨⟨D2OriginalFallbackGroup1175.leaf05884_checked,by decide +kernel,by decide +kernel⟩,⟨⟨D2OriginalFallbackGroup1175.leaf05885_checked,by decide +kernel,by decide +kernel⟩,⟨D2OriginalFallbackGroup1175.leaf05886_checked,by decide +kernel,by decide +kernel⟩⟩⟩,⟨D2OriginalFallbackGroup1175.leaf05887_checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=2)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((37/80) : ℚ) : ℝ)-(((71/160) : ℚ) : ℝ))*(((-64733087483093856127/590295810358705651712) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((71/160) : ℚ) : ℝ)..(((37/80) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 2 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D2OriginalFallbackGroup1175Complete
