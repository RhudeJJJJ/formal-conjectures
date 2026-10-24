/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymbolicAnchor007Source
namespace Gebendorfer.RadenkovicGutman.SymbolicAnchor007Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (90327/134217728)
  b := (1589755/2147483648)
  s := [(4371082082151/4398046511104),(-5340952425/4398046511104),(-127540015/2199023255552)]
  L := [(1990185620723026928179041/618970019642690137449562112),(33712086175/52776558133248),(13125259469/422212465065984),(-8846369/105553116266496),(-25075/13194139533312)]
  c := (226257909699/70368744177664)
  R := (-35873930792791/12500000000000)
  total := (-189907207241/1000000000000000)
  k := 9
  n := 32
  sFloor := (136421439053/274877906944)
  nFloor := (986078607997/36028797018963968)
  eFloor := (471511576773/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1445232,width:=144523,den:=2147483648,localDen:=1856910058928070412348686336,lowerC:=5970556862168224996786176,s:=[1845525340910727692323651584,-2255016689159395029811200,-107697968255405150699520],L:=[5970556862169080784537123,1186138583871969139097600,57725501614970189643776,-155626969265554325504,-3528992520509849600],transformed:=fun i => IntegerPolynomialPaymentCell.affine (SymbolicAnchor007Source.source.poly i) 1445232 144523 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks SymbolicAnchor007Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 16) (CoreQuotient.fused G u 9 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 16 SymbolicAnchor007Source.data
    SymbolicAnchor007Source.path_checked SymbolicAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor007Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 9) (CoreQuotient.fused G u 16 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 9 SymbolicAnchor007Source.data
    SymbolicAnchor007Source.path_swapped SymbolicAnchor007Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry SymbolicAnchor007Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.SymbolicAnchor007Cell127
