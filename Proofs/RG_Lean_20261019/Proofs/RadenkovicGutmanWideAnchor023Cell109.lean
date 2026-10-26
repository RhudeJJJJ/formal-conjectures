/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor023Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor023Cell109
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1669171/1048576)
  b := (500751/262144)
  s := [(3395293853341/70368744177664),(-1182018027133/70368744177664),(102028550685/35184372088832)]
  L := [(22016132971040363291/18446744073709551616),(-17278697237/13194139533312),(-59270870371/6597069766656),(2009598143/824633720832),(-128472737/412316860416)]
  c := (325820571365/274877906944)
  R := (850099054633/10000000000000)
  total := (27742976543089/1000000000000000)
  k := 0
  n := 32
  sFloor := (1208666463789/70368744177664)
  nFloor := 53037566113566042074761920512
  eFloor := 40347833028993540571722153984
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1669171,width:=333833,den:=1048576,localDen:=55340232221128654848,lowerC:=65596345236408238080,s:=[2670167735670669312,-929576801114259456,160477034344611840],L:=[66048398913121089873,-72472108935938048,-497200097361133568,134861848473239552,-17243318870081536],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor023Source.source.poly i) 1669171 333833 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor023Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 32) (CoreQuotient.fused G u 9 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 32 WideAnchor023Source.data
    WideAnchor023Source.path_checked WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 9) (CoreQuotient.fused G u 32 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 9 WideAnchor023Source.data
    WideAnchor023Source.path_swapped WideAnchor023Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor023Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor023Cell109
