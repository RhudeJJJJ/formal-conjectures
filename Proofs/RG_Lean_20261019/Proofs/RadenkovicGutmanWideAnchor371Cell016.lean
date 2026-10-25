/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor371Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor371Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (302913/4398046511104)
  b := (726991/8796093022208)
  s := [(2199023255551/2199023255552),(-3/4398046511104),(1/2199023255552)]
  L := [(3861177484399/38685626227668133590597632),(4633405333175/116056878683004400771792896),(77223294767/19342813113834066795298816),(-11/7253554917687775048237056),(1/1208925819614629174706176)]
  c := (1930588742199/19342813113834066795298816)
  R := (-1496775852346809/100000000000000)
  total := (-102443857/500000000000000)
  k := 44
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (333994452907/4835703278458516698824704)
  eFloor := (671212687871/4835703278458516698824704)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=605826,width:=121165,den:=8796093022208,localDen:=116056878683004400771792896,lowerC:=11583532453194,s:=[116056878682951624213659648,-79164837199872,52776558133248],L:=[11583532453197,4633405333175,463339768602,-176,96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor371Source.source.poly i) 605826 121165 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor371Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 2 10 WideAnchor371Source.data
    WideAnchor371Source.path_checked WideAnchor371Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor371Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((15/8) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (15/8) 10 2 WideAnchor371Source.data
    WideAnchor371Source.path_swapped WideAnchor371Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor371Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor371Cell016
