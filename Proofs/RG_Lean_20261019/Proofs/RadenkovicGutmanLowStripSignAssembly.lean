/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripAssembly
import Proofs.RadenkovicGutmanLowStripCoordinates
import Proofs.RadenkovicGutmanLowStripConstantGeometry
import Proofs.RadenkovicGutmanCorrelatedEscape

/-! Original high-degree analytic assembly from the remaining pointwise signs.
Sources: rg_multiarm_small_ordinate_lowstrip.py,
rg_multiarm_small_ordinate_midstrip.py, and the original direct escape producer.
No sign family or complete OriginalAssembly.Inputs field is supplied here. -/
namespace Gebendorfer.RadenkovicGutman.LowStripSignAssembly
open Real Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

/-- All three original signs for the same C,u and physical arms p+1,q+1. -/
def ActualSigns {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ) : Prop :=
  0 ≤ LowStripGeometry.outside (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c ∧
    0 ≤ LowStripGeometry.directed (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c ∧
    0 ≤ LowStripGeometry.reserve (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c

theorem tangent_graph_lower_of_family {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))))
    (hS : ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) →
      ActualSigns C u p q y c) :
    -arsinh (2/((C.degree u : ℝ)*y))-log 2 ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  let d : ℝ := C.degree u
  have hd0 : 0 < d := by dsimp [d]; exact_mod_cast (by omega : 0 < C.degree u)
  have he : d*(8/(3*d))=8/3 := by field_simp [hd0.ne']
  have hdy : d*y ∈ Ioc (0 : ℝ) (8/3) := by
    refine ⟨mul_pos hd0 hy.1,?_⟩
    have h := mul_le_mul_of_nonneg_left hy.2 hd0.le
    rwa [he] at h
  obtain ⟨c,hc,hrelation⟩ := LowStripCoordinates.tangent_coordinate_exists (d*y) hdy
  obtain ⟨hO,hD,hR⟩ := hS c hc hrelation
  exact LowStripGeometry.tangent_graph_lower_of_actual_signs C u p q y c hy.1 hc hrelation hO hD hR

theorem original_graph_lowstrip_of_sign_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) → ActualSigns C u p q y c)
    (hConstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2), ActualSigns C u p q y 1) :
    (-(8/3 : ℝ)*log 2-2*log 3)/(C.degree u : ℝ)-log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2),
        MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  apply LowStripPrimitive.original_graph_lowstrip_lower C u p q hd
  · intro y hy
    exact tangent_graph_lower_of_family C u p q hd y hy (hTangent y hy)
  · intro y hy
    obtain ⟨hO,hD,hR⟩ := hConstant y hy
    have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
    have hcut : (0 : ℝ) < 8/(3*(C.degree u : ℝ)) := by positivity
    exact LowStripConstantGeometry.graph_lower_of_actual_signs C u p q y
      (lt_of_lt_of_le hcut hy.1) hO hD hR

theorem strict_fusion_of_original_sign_families {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hTree : (source C u p q).IsTree) (hd : 46 ≤ C.degree u)
    (hTangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) → ActualSigns C u p q y c)
    (hConstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2), ActualSigns C u p q y 1)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  exact CorrelatedEscape.strict_fusion_of_lowstrip_and_signs C u p q hTree hd hEscape
    (original_graph_lowstrip_of_sign_families C u p q hd hTangent hConstant)

#print axioms tangent_graph_lower_of_family
#print axioms original_graph_lowstrip_of_sign_families
#print axioms strict_fusion_of_original_sign_families
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripSignAssembly
