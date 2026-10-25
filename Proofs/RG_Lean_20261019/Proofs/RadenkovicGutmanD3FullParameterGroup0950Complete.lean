/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950
import Proofs.RadenkovicGutmanFastArmCoverIntegral
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950Complete
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def cover : FastArmCover.Cover := .leaf D3FullParameterGroup0950.leaf03800
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(4096/5),1024,(3375902963881781/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 3 4 4 (4096/5) 1024 0 1 0 1 (3375902963881781/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,decide_eq_true_eq]
  exact ⟨D3FullParameterGroup0950.leaf03800_checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
open MeasureTheory CoreQuotient ActualFusionIntegral
open scoped Classical
theorem actual_integral_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=3)
    (hp : ArmClasses.classify p=4) (hq : ArmClasses.classify q=4) :
    (((1024 : ℚ) : ℝ)-(((4096/5) : ℚ) : ℝ))*(((3375902963881781/1180591620717411303424) : ℚ) : ℝ) ≤
      ∫ y : ℝ in (((4096/5) : ℚ) : ℝ)..((1024 : ℚ) : ℝ),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y :=
  FastArmCoverIntegral.single_integral_lower C u p q 3 (by decide) hd 4 4 hp hq slice slice_checked
#print axioms cover_checked
#print axioms slice_checked
#print axioms actual_integral_lower
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950Complete
