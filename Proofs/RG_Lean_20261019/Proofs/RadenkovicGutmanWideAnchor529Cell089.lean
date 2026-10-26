/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor529Cell089
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (43539/1048576)
  b := (1671897/33554432)
  s := [(4114286717285/4398046511104),(-51875938435/2199023255552),(-1462350787/1099511627776)]
  L := [(3438214099744426014147/151115727451828646838272),(3822512488835/422212465065984),(186123224569/211106232532992),(-169368275/26388279066624),(-10112761/13194139533312)]
  c := (800521601863/35184372088832)
  R := (-94577344267891/50000000000000)
  total := (-14934624494607/1000000000000000)
  k := 6
  n := 32
  sFloor := (2002342718633/4398046511104)
  nFloor := (662947037061/17592186044416)
  eFloor := (485654960519/8796093022208)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1393248,width:=278649,den:=33554432,localDen:=453347182355485940514816,lowerC:=10314642299229353017344,s:=[424097445530550549872640,-10694662033326452244480,-602951885322706747392],L:=[10314642299233278042441,4104391532024472535040,399696581274959347712,-2909724808419737600,-347471822138114048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor529Source.source.poly i) 1393248 278649 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor529Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 8 WideAnchor529Source.data
    WideAnchor529Source.path_checked WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 8 4 WideAnchor529Source.data
    WideAnchor529Source.path_swapped WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor529Cell089
