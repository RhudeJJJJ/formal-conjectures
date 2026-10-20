/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanHighDegreeInputFromSigns

/-! Exhaustive transfer from the original three arm-parity boxes.
Source: rg_multiarm_small_ordinate_lowstrip.py, parity_enclosure.
The three boxes retain all outside/directed/full-reserve signs as premises. -/
namespace Gebendorfer.RadenkovicGutman.LowStripParityBridge
open Set LowStripGeometry CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

def BoxSigns (d y P Q c : ℝ) : Prop :=
  0 ≤ outside d y P Q c ∧ 0 ≤ directed d y P Q c ∧ 0 ≤ reserve d y P Q c

def oddCoordinate (y a : ℝ) : ℝ := y+(y*a)/y
def evenCoordinate (y a : ℝ) : ℝ := y+((y+a)/(1+y))/y

def ThreeParityBoxes (d y c : ℝ) : Prop :=
  (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
    BoxSigns d y (oddCoordinate y a) (oddCoordinate y b) c) ∧
  (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
    BoxSigns d y (oddCoordinate y a) (evenCoordinate y b) c) ∧
  (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
    BoxSigns d y (evenCoordinate y a) (evenCoordinate y b) c)

theorem boxSigns_swap (d y P Q c : ℝ) : BoxSigns d y Q P c ↔ BoxSigns d y P Q c := by
  have hA : Focus.A Q P=Focus.A P Q := by simp only [Focus.A,mul_comm Q P,add_comm Q P]
  have hB : Focus.B y Q P=Focus.B y P Q := by simp only [Focus.B,mul_comm Q P,add_comm Q P]
  have hN : Focus.N₀ y Q P=Focus.N₀ y P Q := by simp only [Focus.N₀,add_comm Q P]
  have hD : Focus.D₀ y Q P=Focus.D₀ y P Q := by simp only [Focus.D₀,add_comm Q P]
  simp only [BoxSigns,outside,directed,reserve,lead,bx,bt,constant,hA,hB,hN,hD]

/-- Every physical pair belongs to one of the three original boxes, up to swap. -/
theorem actual_signs_of_three_parity_boxes {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ) (hy : 0 < y)
    (h : ThreeParityBoxes (C.degree u) y c) : LowStripSignAssembly.ActualSigns C u p q y c := by
  change BoxSigns (C.degree u) y
    (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c
  rcases LowStripParity.actual_parameter y hy p with ⟨_,a,ha,hp⟩ | ⟨_,a,ha,hp⟩
  · rcases LowStripParity.actual_parameter y hy q with ⟨_,b,hb,hq⟩ | ⟨_,b,hb,hq⟩
    · rw [hp,hq]
      exact h.1 a ha b hb
    · rw [hp,hq]
      exact h.2.1 a ha b hb
  · rcases LowStripParity.actual_parameter y hy q with ⟨_,b,hb,hq⟩ | ⟨_,b,hb,hq⟩
    · rw [hp,hq]
      exact (boxSigns_swap (C.degree u) y (oddCoordinate y b) (evenCoordinate y a) c).mpr
        (h.2.1 b hb a ha)
    · rw [hp,hq]
      exact h.2.2 a ha b hb

theorem original_normalized_target_of_parity_families {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hTangent : ∀ y ∈ Ioc (0 : ℝ) (8/(3*(C.degree u : ℝ))),
      ∀ c ∈ Ioc (0 : ℝ) (1/2), (C.degree u : ℝ)*y=4*c/(1-c^2) →
        ThreeParityBoxes (C.degree u) y c)
    (hConstant : ∀ y ∈ Icc (8/(3*(C.degree u : ℝ)) : ℝ) (1/2),
      ThreeParityBoxes (C.degree u) y 1)
    (hEscape : CorrelatedEscape.Signs (C.degree u)) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 := by
  apply HighDegreeInputFromSigns.normalized_lower_of_original_sign_families C u p q hd
  · intro y hy c hc hr
    exact actual_signs_of_three_parity_boxes C u p q y c hy.1 (hTangent y hy c hc hr)
  · intro y hy
    have hd0 : (0 : ℝ) < C.degree u := by exact_mod_cast (by omega : 0 < C.degree u)
    have hcut : (0 : ℝ) < 8/(3*(C.degree u : ℝ)) := by positivity
    exact actual_signs_of_three_parity_boxes C u p q y 1 (lt_of_lt_of_le hcut hy.1)
      (hConstant y hy)
  · exact hEscape

#print axioms boxSigns_swap
#print axioms actual_signs_of_three_parity_boxes
#print axioms original_normalized_target_of_parity_families
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripParityBridge
