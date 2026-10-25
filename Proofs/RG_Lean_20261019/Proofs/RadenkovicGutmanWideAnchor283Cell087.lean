/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor283Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor283Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (483767/16777216)
  b := (72565/2097152)
  s := [(4282928599219/4398046511104),(-5510319245/549755813888),(-852860773/1099511627776)]
  L := [(4257510830071050906253/302231454903657293676544),(4647640455281/844424930131968),(211097416097/422212465065984),(-495658157/52776558133248),(-6719897/26388279066624)]
  c := (1982557973857/140737488355328)
  R := (-26640677834291/12500000000000)
  total := (-11764264523013/1000000000000000)
  k := 7
  n := 32
  sFloor := (2117717301083/4398046511104)
  nFloor := (1393773745361/70368744177664)
  eFloor := (1312050557183/70368744177664)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=483767,width:=96753,den:=16777216,localDen:=906694364710971881029632,lowerC:=12772532490209756971008,s:=[882961836707937414807552,-9087990123953054023680,-703297752590645723136],L:=[12772532490213152718759,4990365939749611372544,453328249203359481856,-8515342297242533888,-230893902779908096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor283Source.source.poly i) 483767 96753 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor283Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 8) (CoreQuotient.fused G u 0 8) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 0 8 WideAnchor283Source.data
    WideAnchor283Source.path_checked WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 0) (CoreQuotient.fused G u 8 0) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 8 0 WideAnchor283Source.data
    WideAnchor283Source.path_swapped WideAnchor283Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor283Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor283Cell087
