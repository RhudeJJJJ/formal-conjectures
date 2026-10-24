module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Determinant logarithms for graphs with different finite vertex types.
The cardinality premise is explicit; no unproved integrability is assumed.
-/
public import Proofs.RGModernRadenkovicGutmanGraphIntegral
public import Proofs.RGModernRadenkovicGutmanIsoEnergy

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.MixedGraphIntegral
open Matrix Set MeasureTheory
open scoped Classical
noncomputable section
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

def logarithm (G : SimpleGraph V) (H : SimpleGraph W) (t y : ℝ) : ℝ :=
  Real.log ‖(CoreQuotient.shifted ((t : ℂ) + (y : ℂ) * Complex.I) G).det /
    (CoreQuotient.shifted ((t : ℂ) + (y : ℂ) * Complex.I) H).det‖

theorem shifted_det_eq {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (z : ℂ) :
    (CoreQuotient.shifted z G).det = (CoreQuotient.shifted z H).det := by
  have h : Matrix.reindex f.toEquiv f.toEquiv (CoreQuotient.shifted z G) =
      CoreQuotient.shifted z H := by
    change (z • (1 : Matrix V V ℂ) - G.lapMatrix ℂ).submatrix
      f.toEquiv.symm f.toEquiv.symm = z • (1 : Matrix W W ℂ) - H.lapMatrix ℂ
    simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
      Matrix.submatrix_one_equiv]
    rw [show (G.lapMatrix ℂ).submatrix f.toEquiv.symm f.toEquiv.symm = H.lapMatrix ℂ from
      IsoEnergy.laplacian_reindex f]
  rw [← h, Matrix.det_reindex_self]

theorem integrable (G : SimpleGraph V) (H : SimpleGraph W)
    (hc : Fintype.card V = Fintype.card W) (t : ℝ) :
    IntegrableOn (logarithm G H t) (Ioi 0) := by
  let e : V ≃ W := Fintype.equivOfCardEq hc
  let H' : SimpleGraph V := H.comap e
  let f : H' ≃g H := { toEquiv := e, map_rel_iff' := by intro a b; rfl }
  have he : logarithm G H t = GraphIntegral.graphLogarithm G H' t := by
    funext y
    unfold logarithm GraphIntegral.graphLogarithm
    rw [shifted_det_eq f]
  rw [he]
  exact GraphIntegral.graph_integrable G H' t

#print axioms shifted_det_eq
#print axioms integrable

attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.MixedGraphIntegral
