/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor426Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor426Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1612557/67108864)
  b := (483767/16777216)
  s := [(4329551486333/4398046511104),(-13407417231/2199023255552),(-593075853/1099511627776)]
  L := [(427329052632079184668321/77371252455336267181195264),(7438346159915/3377699720527872),(367171519483/1688849860263936),(-118058681/211106232532992),(-2875831/105553116266496)]
  c := (777307018565/140737488355328)
  R := (-51988162437597/20000000000000)
  total := (-1204336187771/100000000000000)
  k := 8
  n := 32
  sFloor := (2150182174229/4398046511104)
  nFloor := (627946766301/70368744177664)
  eFloor := (27883953523/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1612557,width:=322511,den:=67108864,localDen:=232113757366008801543585792,lowerC:=1281987157896168902492160,s:=[228498825709343858264899584,-1415194669817164858392576,-125202008933120581042176],L:=[1281987157896237554004963,511159255890593778237440,50463669382467578494976,-129806892519397523456,-6324019248037363712],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor426Source.source.poly i) 1612557 322511 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor426Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 6 WideAnchor426Source.data
    WideAnchor426Source.path_checked WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 6 2 WideAnchor426Source.data
    WideAnchor426Source.path_swapped WideAnchor426Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor426Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor426Cell086
