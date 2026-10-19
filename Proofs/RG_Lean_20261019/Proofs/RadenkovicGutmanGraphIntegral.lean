/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Actual graph determinant integrals and the strict comparison from an integral
reserve. No uniform positive reserve is assumed implicitly or claimed here.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Sections 2.1--2.3.
-/
import Proofs.RadenkovicGutmanCoulson
import Proofs.RadenkovicGutmanCountTransport
import Proofs.RadenkovicGutmanFusionQuotient

set_option backward.isDefEq.respectTransparency false

namespace Gebendorfer.RadenkovicGutman.GraphIntegral

open Matrix Set MeasureTheory
open scoped Classical
noncomputable section

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem complex_laplacian (G : SimpleGraph V) :
    (G.lapMatrix ℝ).map Complex.ofRealHom = G.lapMatrix ℂ := by
  ext i j
  by_cases hij : i = j <;> by_cases ha : G.Adj i j <;>
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
      hij, ha]

def graphLogarithm (G H : SimpleGraph V) (t y : ℝ) : ℝ :=
  Real.log ‖(CoreQuotient.shifted ((t : ℂ) + (y : ℂ) * Complex.I) G).det /
    (CoreQuotient.shifted ((t : ℂ) + (y : ℂ) * Complex.I) H).det‖

theorem graphLogarithm_eq (G H : SimpleGraph V) (t : ℝ) :
    graphLogarithm G H t = Coulson.matrixLogarithm (G.lapMatrix ℝ) (H.lapMatrix ℝ) t := by
  funext y
  simp only [graphLogarithm, Coulson.matrixLogarithm, complex_laplacian, CoreQuotient.shifted]

theorem graph_integrable (G H : SimpleGraph V) (t : ℝ) :
    IntegrableOn (graphLogarithm G H t) (Ioi 0) := by
  rw [graphLogarithm_eq G H t]
  exact Coulson.matrix_integrable _ _ (G.isHermitian_lapMatrix ℝ)
    (H.isHermitian_lapMatrix ℝ) t

theorem graph_stopLoss_integral (G H : SimpleGraph V) (he : G.edgeFinset.card = H.edgeFinset.card) (t : ℝ) :
    (1 / Real.pi) * (∫ y : ℝ in Ioi 0, graphLogarithm G H t y) =
      stopLoss (laplacianSpectrum G) t - stopLoss (laplacianSpectrum H) t := by
  rw [graphLogarithm_eq G H t]
  exact Coulson.matrix_stopLoss_integral _ _ (G.isHermitian_lapMatrix ℝ)
    (H.isHermitian_lapMatrix ℝ) (by rw [laplacian_trace, laplacian_trace, he]) t

/-- The exact remaining analytic premise, separated from the count-gap theorem. -/
theorem strict_graphs_of_count_gap_and_reserve (T F : SimpleGraph V)
    (hT : T.IsTree) (hF : F.IsTree)
    (hc : ∀ t, |aboveCount (laplacianSpectrum T) t - aboveCount (laplacianSpectrum F) t| ≤ 1)
    (hreserve : 2 / (Fintype.card V : ℝ) <
      (1 / Real.pi) * (∫ y : ℝ in Ioi 0, graphLogarithm T F 2 y)) :
    laplacianEnergy F < laplacianEnergy T := by
  have hn := hT.connected.nonempty
  have he : T.edgeFinset.card = F.edgeFinset.card := by
    have hs := hT.card_edgeFinset
    have hf := hF.card_edgeFinset
    omega
  rw [graph_stopLoss_integral T F he 2] at hreserve
  have ht := stopLoss_difference_lipschitz (laplacianSpectrum T) (laplacianSpectrum F) hc
    (2 - 2 / (Fintype.card V : ℝ)) 2
  have habs : |(2 - 2 / (Fintype.card V : ℝ)) - 2| =
      2 / (Fintype.card V : ℝ) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs, abs_le] at ht
  apply (strict_comparison_iff T F he).mpr
  rw [tree_meanDegree T hT]
  linarith [ht.1]

#print axioms graph_integrable
#print axioms graph_stopLoss_integral
#print axioms strict_graphs_of_count_gap_and_reserve

attribute [instance] SimpleGraph.fintypeEdgeSetSup

end
end Gebendorfer.RadenkovicGutman.GraphIntegral
