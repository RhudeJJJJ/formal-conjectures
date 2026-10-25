/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor013Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor013Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (224651/1048576)
  b := (269581/1048576)
  s := [(4873408539699/17592186044416),(-32898999493/4398046511104),(-3938759409/2199023255552)]
  L := [(817651320221986526087/1180591620717411303424),(237718641315/8796093022208),(47296217843/13194139533312),(-322828727/549755813888),(23667877/824633720832)]
  c := (1522994265373/2199023255552)
  R := (-1836674892363/10000000000000)
  total := (-7425580028551/1000000000000000)
  k := 1
  n := 32
  sFloor := (1177575616613/8796093022208)
  nFloor := (489363110813/1073741824)
  eFloor := (800055698757/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=224651,width:=44930,den:=1048576,localDen:=3541774862152233910272,lowerC:=2452953960664717590528,s:=[981146732721296375808,-26493773792541671424,-6343816068175233024],L:=[2452953960665959578261,95718167821638696960,12695981803761041408,-2079808237011468288,101652757680750592],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor013Source.source.poly i) 224651 44930 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor013Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 22) (CoreQuotient.fused G u 9 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 22 WideAnchor013Source.data
    WideAnchor013Source.path_checked WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 9) (CoreQuotient.fused G u 22 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 9 WideAnchor013Source.data
    WideAnchor013Source.path_swapped WideAnchor013Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor013Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor013Cell098
