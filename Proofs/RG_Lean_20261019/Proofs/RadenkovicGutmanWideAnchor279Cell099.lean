/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor279Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor279Cell099
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (269581/1048576)
  b := (323497/1048576)
  s := [(279818875629/549755813888),(-659276986141/8796093022208),(35442186639/4398046511104)]
  L := [(35002071278517390037/73786976294838206464),(1475147811137/13194139533312),(-17761618541/3298534883328),(-361957193/824633720832),(21983765/206158430208)]
  c := (1043143012479/2199023255552)
  R := (-9322187549243/25000000000000)
  total := (-8222242032119/500000000000000)
  k := 2
  n := 32
  sFloor := (243044337325/1099511627776)
  nFloor := (38810208635/8589934592)
  eFloor := (26621879321/8589934592)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=269581,width:=53916,den:=1048576,localDen:=221360928884514619392,lowerC:=105006213835505270784,s:=[112669961215316852736,-16591248600474845184,1783863662264451072],L:=[105006213835552170111,24748873459372654592,-1191962043087847424,-97162144155435008,23604887929487360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor279Source.source.poly i) 269581 53916 1048576
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor279Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 0 6 WideAnchor279Source.data
    WideAnchor279Source.path_checked WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 6 0 WideAnchor279Source.data
    WideAnchor279Source.path_swapped WideAnchor279Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor279Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor279Cell099
