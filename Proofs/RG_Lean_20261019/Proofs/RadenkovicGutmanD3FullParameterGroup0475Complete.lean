/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .leaf D3FullParameterGroup0475.leaf01900
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(559/12800),(281/6400),(-8600695753426310452355/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 3 4 4 (559/12800) (281/6400) 0 1 0 1 (-8600695753426310452355/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,decide_eq_true_eq]
  exact ⟨D3FullParameterGroup0475.leaf01900_checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=3)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    ((((281/6400) : ℚ) : ℝ)-(((559/12800) : ℚ) : ℝ))*(((-8600695753426310452355/4722366482869645213696) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((559/12800) : ℚ) : ℝ)..(((281/6400) : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 3 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475Complete
