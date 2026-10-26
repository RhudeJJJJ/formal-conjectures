/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor530Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor530Cell069
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (581469/536870912)
  b := (1395525/1073741824)
  s := [(4397796255387/4398046511104),(-100092801/4398046511104),(-5002067/2199023255552)]
  L := [(3228292030105/288230376151711744),(1937013764903/432345564227567616),(193718292833/432345564227567616),(435335/54043195528445952),(10873/27021597764222976)]
  c := (403536503763/36028797018963968)
  R := (-569978107120921/100000000000000)
  total := (-1214345479267/1000000000000000)
  k := 17
  n := 32
  sFloor := (1099421539613/2199023255552)
  nFloor := (975743525979/72057594037927936)
  eFloor := (1239307754451/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1162938,width:=232587,den:=1073741824,localDen:=864691128455135232,lowerC:=9684876090312,s:=[864641926179127296,-19679045419008,-1966892777472],L:=[9684876090315,3874027529806,387436585666,6965360,347936],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor530Source.source.poly i) 1162938 232587 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor530Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 8 WideAnchor530Source.data
    WideAnchor530Source.path_checked WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 8 4 WideAnchor530Source.data
    WideAnchor530Source.path_swapped WideAnchor530Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor530Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor530Cell069
