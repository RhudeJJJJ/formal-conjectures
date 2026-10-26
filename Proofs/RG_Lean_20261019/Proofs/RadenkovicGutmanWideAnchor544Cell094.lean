/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor544Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor544Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (433355/4194304)
  b := (260013/2097152)
  s := [(7005261927975/35184372088832),(422908172475/35184372088832),(-19961869695/17592186044416)]
  L := [(883052033121734116473/1180591620717411303424),(-15340106133/2199023255552),(1383947501/1649267441664),(27282805/137438953472),(-3451391/103079215104)]
  c := (1631680638419/2199023255552)
  R := (-14920136843991/100000000000000)
  total := (-3044117231551/1000000000000000)
  k := 1
  n := 32
  sFloor := (1751315481993/17592186044416)
  nFloor := (5997803903/2147483648)
  eFloor := (10711669489/4294967296)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=433355,width:=86671,den:=4194304,localDen:=3541774862152233910272,lowerC:=2628005617322252304384,s:=[705172755013278105600,42571330546669977600,-4018855195642429440],L:=[2649156099365202349419,-24706970309401509888,2972004628087963648,703072531308871680,-118588891765669888],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor544Source.source.poly i) 433355 86671 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor544Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 22) (CoreQuotient.fused G u 5 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 22 WideAnchor544Source.data
    WideAnchor544Source.path_checked WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 5) (CoreQuotient.fused G u 22 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 5 WideAnchor544Source.data
    WideAnchor544Source.path_swapped WideAnchor544Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor544Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor544Cell094
