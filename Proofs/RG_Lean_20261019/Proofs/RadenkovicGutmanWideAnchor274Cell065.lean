/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor274Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor274Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (560831/1073741824)
  b := (672997/1073741824)
  s := [(34359604993/34359738368),(-6828757/4398046511104),(-341427/2199023255552)]
  L := [(3429391799271/1152921504606846976),(4115251212371/3458764513820540928),(205759871939/1729382256910270464),(-58043/216172782113783808),(-1451/108086391056891904)]
  c := (1714695899635/576460752303423488)
  R := (-318135669755253/50000000000000)
  total := (-5116210133/7812500000000)
  k := 19
  n := 32
  sFloor := (1099505481873/2199023255552)
  nFloor := (443433108257/72057594037927936)
  eFloor := (1157353863851/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=560831,width:=112166,den:=1073741824,localDen:=3458764513820540928,lowerC:=10288175397810,s:=[3458751087853436928,-5370353025024,-537018236928],L:=[10288175397813,4115251212371,411519743878,-928688,-46432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor274Source.source.poly i) 560831 112166 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor274Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 4) (CoreQuotient.fused G u 0 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 0 4 WideAnchor274Source.data
    WideAnchor274Source.path_checked WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 0) (CoreQuotient.fused G u 4 0) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 0 WideAnchor274Source.data
    WideAnchor274Source.path_swapped WideAnchor274Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor274Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor274Cell065
