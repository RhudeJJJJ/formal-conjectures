/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor374Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor374Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (560831/1073741824)
  b := (672997/1073741824)
  s := [(137435947381/137438953472),(-38476189/4398046511104),(-1923333/2199023255552)]
  L := [(2089942982645/288230376151711744),(5015737567429/1729382256910270464),(83587700933/288230376151711744),(-583159/108086391056891904),(-4857/18014398509481984)]
  c := (2089942982645/288230376151711744)
  R := (-29585946429937/5000000000000)
  total := (-304167229091/500000000000000)
  k := 18
  n := 32
  sFloor := (549738499167/1099511627776)
  nFloor := (436370588707/72057594037927936)
  eFloor := (1316308885255/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=560831,width:=112166,den:=1073741824,localDen:=1729382256910270464,lowerC:=12539657895870,s:=[1729344431531753472,-15129453133824,-1512570617856],L:=[12539657895870,5015737567429,501526205598,-9330544,-466272],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor374Source.source.poly i) 560831 112166 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor374Source.source witness geometry=true := by
  unfold IntegerPolynomialPaymentCell.checks
  rw [decide_eq_true_eq]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by intro i; rfl,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩
theorem budget : SemanticPolynomialPaymentCell.Budget witness := by
  unfold SemanticPolynomialPaymentCell.Budget
  decide +kernel
theorem logarithm_checked : RationalLog.accepts witness.c witness.R witness.k witness.n=true := by decide +kernel
noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 12) (CoreQuotient.fused G u 2 12) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 12 WideAnchor374Source.data
    WideAnchor374Source.path_checked WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 2) (CoreQuotient.fused G u 12 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 12 2 WideAnchor374Source.data
    WideAnchor374Source.path_swapped WideAnchor374Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor374Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor374Cell065
