/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripDirected
import Proofs.RadenkovicGutmanHighDegreeInputFromTwoSigns
/-! Exact original degree46 target, retaining only the original full reserve
families in the low strips. The original escape signs remain separate inputs. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeInputFromReserves
open Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

def ActualReserve {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ) : Prop :=
  0 ≤ LowStripGeometry.reserve (C.degree u) y
    (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c

theorem normalized_target_of_reserve_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) → ActualReserve C u p q y c)
    (hConstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2), ActualReserve C u p q y 1)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 := by
  apply HighDegreeInputFromTwoSigns.normalized_target_of_two_sign_families C u p q hd
  · intro y hy c hc hr
    exact ⟨LowStripDirected.actual_tangent_directed C u p q (by omega) y c hy.1 ⟨hc.1.le,hc.2⟩,
      hTangent y hy c hc hr⟩
  · intro y hy
    have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
    have hcut : (0 : ℝ) < 8/(3*(C.degree u : ℝ)) := by positivity
    exact ⟨LowStripDirected.actual_constant_directed C u p q (by omega) y (lt_of_lt_of_le hcut hy.1),
      hConstant y hy⟩
  · exact hEscape

#print axioms normalized_target_of_reserve_families
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeInputFromReserves
