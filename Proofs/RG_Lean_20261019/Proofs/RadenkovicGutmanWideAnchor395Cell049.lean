/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor395Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor395Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (970699/34359738368)
  b := (582419/17179869184)
  s := [(2199023232567/2199023255552),(-9193/2199023255552),(-115/274877906944)]
  L := [(1188971447271842015704112751/166153499473114484112975882535043072),(633608653967/221360928884514619392),(126721205663/442721857769029238784),(-43/27670116110564327424),(1/27670116110564327424)]
  c := (528009390553/73786976294838206464)
  R := (-937766700566181/100000000000000)
  total := (-26227991313/500000000000000)
  k := 28
  n := 32
  sFloor := (1099511611227/2199023255552)
  nFloor := (293394084437/18446744073709551616)
  eFloor := (857089620067/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=970699,width:=194139,den:=34359738368,localDen:=498460498419343452338927647605129216,lowerC:=3566914341813920236339986432,s:=[498460493209250959118505476238606336,-2083810323696991125576351744,-208539703883523532636815360],L:=[3566914341815526047112338253,1426759848952251371084578816,142675393650956696878579712,-774619135907725312,18014398509481984],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor395Source.source.poly i) 970699 194139 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor395Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 2 2 WideAnchor395Source.data
    WideAnchor395Source.path_checked WideAnchor395Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor395Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 2 2 WideAnchor395Source.data
    WideAnchor395Source.path_swapped WideAnchor395Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor395Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor395Cell049
