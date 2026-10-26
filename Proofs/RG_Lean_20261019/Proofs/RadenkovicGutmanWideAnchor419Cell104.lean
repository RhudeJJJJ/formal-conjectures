/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor419Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor419Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (670803/1048576)
  b := (1609927/2097152)
  s := [(6458987650067/35184372088832),(-98302115469/2199023255552),(59827001407/8796093022208)]
  L := [(141604386244393158701/147573952589676412928),(636960620645/6597069766656),(-15752778649/824633720832),(1090052641/412316860416),(-13132547/51539607552)]
  c := (2110069785183/2199023255552)
  R := (-1032306663543/50000000000000)
  total := (7198323393/62500000000000)
  k := 1
  n := 32
  sFloor := (1281365452047/17592186044416)
  nFloor := (471326825643/1073741824)
  eFloor := (169412409453/536870912)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1341606,width:=268321,den:=2097152,localDen:=442721857769029238784,lowerC:=424813158733065486336,s:=[81272873209879855104,-19790829893764251648,3011191575712628736],L:=[424813158733179476103,42745703664220897280,-8457208639822757888,1170435111003357184,-112807719756365824],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor419Source.source.poly i) 1341606 268321 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor419Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 4 WideAnchor419Source.data
    WideAnchor419Source.path_checked WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 2 WideAnchor419Source.data
    WideAnchor419Source.path_swapped WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor419Cell104
