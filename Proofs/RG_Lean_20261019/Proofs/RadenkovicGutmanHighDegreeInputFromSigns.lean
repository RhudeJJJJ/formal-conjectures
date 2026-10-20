/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripSignAssembly

/-! Exact normalized target of OriginalAssembly.Inputs.degreeGeFortysix.
Source: unified manuscript, original degree-46 scalar reserve and coverage table.
The original three sign families remain hypotheses; no Input field is supplied. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeInputFromSigns
open Real Set CoreQuotient LowStripSignAssembly LargeDegreeReserve
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

abbrev TangentSigns {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) : Prop :=
  ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
    ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) → ActualSigns C u p q y c

abbrev ConstantSigns {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) : Prop :=
  ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2), ActualSigns C u p q y 1

theorem integral_lower_of_original_sign_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : TangentSigns C u p q) (hConstant : ConstantSigns C u p q)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    reserveAt (C.degree u) ≤ ∫ y : ℝ in Ioi 0,
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hd' : (46 : ℝ) ≤ C.degree u := by exact_mod_cast hd
  apply TailIntegral.four_region_lower _ (C.degree u) hd'
    (ActualFusionIntegral.logarithm_integrable C u p q 2)
    (original_graph_lowstrip_of_sign_families C u p q hd hTangent hConstant)
  · intro y hy
    exact HighDegreeTail.graph_lower C u p q hd y hy.1
  · exact CorrelatedEscape.graph_lower_of_signs C u p q hd hEscape
  · intro y hy
    apply HighDegreeTail.graph_lower C u p q hd y
    change 10*(C.degree u : ℝ) < y at hy
    linarith only [hd',hy]

/-- The exact original normalized reserve, conditional only on the original signs. -/
theorem normalized_lower_of_original_sign_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : TangentSigns C u p q) (hConstant : ConstantSigns C u p q)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 := by
  have hd' : (46 : ℝ) ≤ C.degree u := by exact_mod_cast hd
  have h := integral_lower_of_original_sign_families C u p q hd hTangent hConstant hEscape
  calc
    (2/47 : ℝ) < reserveAt (C.degree u)/Real.pi := uniform_transport_paid _ hd'
    _ = (1/Real.pi)*reserveAt (C.degree u) := by ring
    _ ≤ (1/Real.pi)*(∫ y : ℝ in Ioi 0,
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :=
      mul_le_mul_of_nonneg_left h (one_div_pos.mpr Real.pi_pos).le
    _ = ActualFusionIntegral.normalizedIntegral C u p q 2 := rfl

#print axioms integral_lower_of_original_sign_families
#print axioms normalized_lower_of_original_sign_families
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeInputFromSigns
