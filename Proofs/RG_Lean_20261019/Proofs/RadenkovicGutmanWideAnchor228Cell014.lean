/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor228Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor228Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (841425/17592186044416)
  b := (504855/8796093022208)
  s := [(2199023255551/2199023255552)]
  L := [(3807461638843/38685626227668133590597632),(4568953966643/116056878683004400771792896),(76149232753/19342813113834066795298816),(13/7253554917687775048237056),(-1/1208925819614629174706176)]
  c := (1903730819421/19342813113834066795298816)
  R := (-1497476325054339/100000000000000)
  total := (-1138803/8000000000000)
  k := 44
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (1047342391907/19342813113834066795298816)
  eFloor := (650192288023/9671406556917033397649408)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=841425,width:=168285,den:=17592186044416,localDen:=116056878683004400771792896,lowerC:=11422384916526,s:=[116056878682951624213659648],L:=[11422384916529,4568953966643,456895396518,208,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor228Source.source.poly i) 841425 168285 17592186044416
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor228Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 12) (CoreQuotient.fused G u 0 12) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 0 12 WideAnchor228Source.data
    WideAnchor228Source.path_checked WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 12 0) (CoreQuotient.fused G u 12 0) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 12 0 WideAnchor228Source.data
    WideAnchor228Source.path_swapped WideAnchor228Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor228Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor228Cell014
