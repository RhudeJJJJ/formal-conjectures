/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor267Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor267Cell024
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (651233/2199023255552)
  b := (1562959/4398046511104)
  s := [(1099511627683/1099511627776),(-37/1099511627776),(-1/274877906944)]
  L := [(7044310479107/151115727451828646838272),(8453166083377/453347182355485940514816),(422657979293/226673591177742970257408),(11/28334198897217871282176),(-5/14167099448608935641088)]
  c := (27516837809/590295810358705651712)
  R := (-1189454576021151/100000000000000)
  total := (-87369167/125000000000000)
  k := 35
  n := 32
  sFloor := (549755813821/1099511627776)
  nFloor := (681333748805/75557863725914323419136)
  eFloor := (617471490859/75557863725914323419136)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1302466,width:=260493,den:=4398046511104,localDen:=453347182355485940514816,lowerC:=21132931437312,s:=[453347182317140472496128,-15255723835392,-1649267441664],L:=[21132931437321,8453166083377,845315958586,176,-160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor267Source.source.poly i) 1302466 260493 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor267Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 43) (CoreQuotient.fused G u 0 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 43 WideAnchor267Source.data
    WideAnchor267Source.path_checked WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 0) (CoreQuotient.fused G u 43 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 0 WideAnchor267Source.data
    WideAnchor267Source.path_swapped WideAnchor267Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor267Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor267Cell024
