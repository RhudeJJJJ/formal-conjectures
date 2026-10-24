/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor009Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor009Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(1092509917135/1099511627776),(-5545483159/4398046511104),(-132201315/2199023255552)]
  L := [(1035245078707282256824235/309485009821345068724781056),(748035469869/1125899906842624),(54554628253/1688849860263936),(-6343817/70368744177664),(-214981/105553116266496)]
  c := (1883099828241/562949953421312)
  R := (-57002714677101/20000000000000)
  total := (-11786058161/62500000000000)
  k := 9
  n := 32
  sFloor := (2182114891375/4398046511104)
  nFloor := (527584019297/18014398509481984)
  eFloor := (2015150133095/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=928455029464035206174343168,lowerC:=3105735236120951887233024,s:=[922542610445204524294471680,-1170686057271645047881728,-55817043091114646568960],L:=[3105735236121846770472705,616855272832386893611008,29991724056585294577664,-83701206671796731904,-1890992874007298048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor009Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor009Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 18) (CoreQuotient.fused G u 9 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 18 SymbolicAnchor009Source.data
    SymbolicAnchor009Source.path_checked SymbolicAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor009Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 9) (CoreQuotient.fused G u 18 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 9 SymbolicAnchor009Source.data
    SymbolicAnchor009Source.path_swapped SymbolicAnchor009Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor009Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor009Cell127
