/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor534Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor534Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (224651/1048576)
  b := (269581/1048576)
  s := [(4256081905755/17592186044416),(-25135054865/17592186044416),(-16860896791/8796093022208)]
  L := [(53619395063857020575/73786976294838206464),(294431500613/13194139533312),(19586155849/6597069766656),(-417080627/824633720832),(20868419/412316860416)]
  c := (798991248963/1099511627776)
  R := (-15963569611599/100000000000000)
  total := (-811172119147/125000000000000)
  k := 1
  n := 32
  sFloor := (1049306264327/8796093022208)
  nFloor := (191059084203/8589934592)
  eFloor := (320972212925/17179869184)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=224651,width:=44930,den:=1048576,localDen:=221360928884514619392,lowerC:=160858185191544324096,s:=[53553904084907458560,-316272183481466880,-424318361124470784],L:=[160858185191571061725,4939740882988433408,657202334576672768,-111959228297510912,11203647140528128],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor534Source.source.poly i) 224651 44930 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor534Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 12) (CoreQuotient.fused G u 5 12) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 12 WideAnchor534Source.data
    WideAnchor534Source.path_checked WideAnchor534Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor534Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 5) (CoreQuotient.fused G u 12 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 12 5 WideAnchor534Source.data
    WideAnchor534Source.path_swapped WideAnchor534Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor534Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor534Cell098
