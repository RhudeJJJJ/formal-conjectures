/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor253Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor253Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (970699/34359738368)
  b := (582419/17179869184)
  s := [(4398045388901/4398046511104),(-448881/4398046511104),(-22443/2199023255552)]
  L := [(80517411222031249958418021/649037107316853453566312041152512),(2746118338079/55340232221128654848),(45768363359/9223372036854775808),(-6515/3458764513820540928),(-55/576460752303423488)]
  c := (143027654115/1152921504606846976)
  R := (-795126349983369/100000000000000)
  total := (-22198267081/500000000000000)
  k := 23
  n := 32
  sFloor := (2199022447567/4398046511104)
  nFloor := (941568574503/18446744073709551616)
  eFloor := (968307393297/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=970699,width:=194139,den:=34359738368,localDen:=1947111321950560360698936123457536,lowerC:=241552233665996320816496640,s:=[1947110825126763406721017272336384,-198729430237219613734600704,-19872013307820646412058624],L:=[241552233666093749875254063,96620449406936485596233728,9661986757919524811440128,-3667618946539847680,-185773484629032960],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor253Source.source.poly i) 970699 194139 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor253Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 30) (CoreQuotient.fused G u 0 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 30 WideAnchor253Source.data
    WideAnchor253Source.path_checked WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 0) (CoreQuotient.fused G u 30 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 0 WideAnchor253Source.data
    WideAnchor253Source.path_swapped WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor253Cell049
