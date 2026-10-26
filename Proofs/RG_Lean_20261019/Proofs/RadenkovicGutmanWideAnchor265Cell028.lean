/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor265Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor265Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (337599/549755813888)
  b := (1620475/2199023255552)
  s := [(1099511627355/1099511627776),(-675/4398046511104),(-33/2199023255552)]
  L := [(1125202142262310156351291971/5316911983139663491615228241121378304),(4797021694741/56668397794435742564352),(79950302109/9444732965739290427392),(-7/3541774862152233910272),(-1/590295810358705651712)]
  c := (1998760521115/9444732965739290427392)
  R := (-222761958159479/20000000000000)
  total := (-1356443679/1000000000000000)
  k := 33
  n := 32
  sFloor := (2199023254339/4398046511104)
  nFloor := (351491688921/9444732965739290427392)
  eFloor := (158975809423/4722366482869645213696)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1350396,width:=270079,den:=2199023255552,localDen:=15950735949418990474845684723364134912,lowerC:=3375606426786139650801008640,s:=[15950735943311497234152578132748533760,-2448074784719624078780006400,-239367312283696576591822848],L:=[3375606426786930469053875913,1350241569807734550713860096,135024056544844117677441024,-31525197391593472,-27021597764222976],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor265Source.source.poly i) 1350396 270079 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor265Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 41) (CoreQuotient.fused G u 0 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 41 WideAnchor265Source.data
    WideAnchor265Source.path_checked WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 0) (CoreQuotient.fused G u 41 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 0 WideAnchor265Source.data
    WideAnchor265Source.path_swapped WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor265Cell028
