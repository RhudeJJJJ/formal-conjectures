/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor014Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor014Cell065
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (560831/1073741824)
  b := (672997/1073741824)
  s := [(4334337034537/4398046511104),(-24944351449/4398046511104),(-1103991619/2199023255552)]
  L := [(1618992738902279378391/151115727451828646838272),(3564787296373/844424930131968),(167651472709/422212465065984),(-255625555/52776558133248),(-4868473/26388279066624)]
  c := (753902242939/70368744177664)
  R := (-56703022006039/25000000000000)
  total := (-113653101367/500000000000000)
  k := 7
  n := 32
  sFloor := (2153592349925/4398046511104)
  nFloor := (2011519689773/72057594037927936)
  eFloor := (85613116003/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=560831,width:=112166,den:=1073741824,localDen:=453347182355485940514816,lowerC:=4856978216706077884416,s:=[446780059516272900046848,-2571244168641245085696,-227597179135828426752],L:=[4856978216706838135173,1913830606889786802176,180014398102847881216,-2195806797493698560,-83639729265836032],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor014Source.source.poly i) 560831 112166 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor014Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 23) (CoreQuotient.fused G u 9 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 23 WideAnchor014Source.data
    WideAnchor014Source.path_checked WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 9) (CoreQuotient.fused G u 23 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 9 WideAnchor014Source.data
    WideAnchor014Source.path_swapped WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor014Cell065
