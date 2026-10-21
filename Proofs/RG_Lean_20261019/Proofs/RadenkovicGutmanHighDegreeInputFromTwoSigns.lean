/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripOutside
import Proofs.RadenkovicGutmanHighDegreeInputFromSigns

/-! The exact original high-degree target after proving the outside condition.
The original directed and complete reserve signs remain hypotheses.
Source: original low/constant-strip conditions and OriginalAssembly.Inputs. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeInputFromTwoSigns
open Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

def ActualRemainingSigns {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ) : Prop :=
  0 ≤ LowStripGeometry.directed (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c ∧
    0 ≤ LowStripGeometry.reserve (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c

theorem normalized_target_of_two_sign_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) →
        ActualRemainingSigns C u p q y c)
    (hConstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2),
      ActualRemainingSigns C u p q y 1)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 := by
  apply HighDegreeInputFromSigns.normalized_lower_of_original_sign_families C u p q hd
  · intro y hy c hc hr
    refine ⟨LowStripOutside.actual_tangent_outside C u p q y c hy.1 ⟨hc.1.le,hc.2⟩,?_⟩
    exact hTangent y hy c hc hr
  · intro y hy
    have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
    have hcut : (0 : ℝ) < 8/(3*(C.degree u : ℝ)) := by positivity
    refine ⟨LowStripOutside.actual_constant_outside C u p q y (lt_of_lt_of_le hcut hy.1),?_⟩
    exact hConstant y hy
  · exact hEscape

#print axioms normalized_target_of_two_sign_families
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeInputFromTwoSigns
