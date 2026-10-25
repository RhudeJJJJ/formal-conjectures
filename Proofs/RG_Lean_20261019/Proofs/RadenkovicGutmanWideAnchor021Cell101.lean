/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor021Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor021Cell101
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1552785/4194304)
  b := (931671/2097152)
  s := [(4117396519245/17592186044416),(-12840554893/549755813888),(1203900883/2199023255552)]
  L := [(60184815305567859165/73786976294838206464),(1628428443931/26388279066624),(-12189976103/13194139533312),(-1387429153/1649267441664),(114081923/824633720832)]
  c := (448411817145/549755813888)
  R := (-2037621600153/20000000000000)
  total := (-30990885321/5000000000000)
  k := 1
  n := 32
  sFloor := (929032492433/8796093022208)
  nFloor := (115630108311/32768)
  eFloor := (1407842811569/524288)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1552785,width:=310557,den:=4194304,localDen:=221360928884514619392,lowerC:=180554445916660039680,s:=[51808838070766141440,-5170290311993229312,121188630940090368],L:=[180554445916703577495,13660247872187138048,-204513862114869248,-186217588676624384,30623633021861888],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor021Source.source.poly i) 1552785 310557 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor021Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 30) (CoreQuotient.fused G u 9 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 30 WideAnchor021Source.data
    WideAnchor021Source.path_checked WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 9) (CoreQuotient.fused G u 30 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 9 WideAnchor021Source.data
    WideAnchor021Source.path_swapped WideAnchor021Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor021Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor021Cell101
