/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor264Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor264Cell105
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1609927/2097152)
  b := (241489/262144)
  s := [(6363075735479/35184372088832),(-1524003734845/35184372088832),(94555078809/17592186044416)]
  L := [(668791358616952543653/590295810358705651712),(1025535698939/13194139533312),(-40824715289/2199023255552),(1628712847/824633720832),(-12498059/137438953472)]
  c := (1245720979975/1099511627776)
  R := (24969671243/400000000000)
  total := (589471993579/50000000000000)
  k := 0
  n := 32
  sFloor := (1257045539563/17592186044416)
  nFloor := 248023102144768
  eFloor := 151858929207808
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1609927,width:=321985,den:=2097152,localDen:=1770887431076116955136,lowerC:=2006374075850135961600,s:=[320264088115470139392,-76705619532903874560,9518225886453694464],L:=[2006374075850857630959,137645071494484590592,-32876403194018660352,3497634206220025856,-161036264005435392],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor264Source.source.poly i) 1609927 321985 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor264Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 40) (CoreQuotient.fused G u 0 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 40 WideAnchor264Source.data
    WideAnchor264Source.path_checked WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 0) (CoreQuotient.fused G u 40 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 0 WideAnchor264Source.data
    WideAnchor264Source.path_swapped WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor264Cell105
