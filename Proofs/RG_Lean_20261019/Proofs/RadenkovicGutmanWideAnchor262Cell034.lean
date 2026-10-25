/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor262Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor262Cell034
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (15751/8589934592)
  b := (302419/137438953472)
  s := [(4398045199119/4398046511104),(-262395/2199023255552),(-205/17179869184)]
  L := [(5781330198949/36893488147419103232),(6937566609725/110680464442257309696),(115625511339/18446744073709551616),(-10511/6917529027641081856),(-87/1152921504606846976)]
  c := (1445332549737/9223372036854775808)
  R := (-783445591301753/100000000000000)
  total := (-2838756361/1000000000000000)
  k := 23
  n := 32
  sFloor := (549755577731/1099511627776)
  nFloor := (933956795635/18889465931478580854784)
  eFloor := (444485508913/9444732965739290427392)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=252016,width:=50403,den:=137438953472,localDen:=110680464442257309696,lowerC:=17343990596844,s:=[110680431425073709056,-13206772776960,-1320702443520],L:=[17343990596847,6937566609725,693753068034,-168176,-8352],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor262Source.source.poly i) 252016 50403 137438953472
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor262Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 3) (CoreQuotient.fused G u 0 3) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 3 WideAnchor262Source.data
    WideAnchor262Source.path_checked WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 3 0) (CoreQuotient.fused G u 3 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 3 0 WideAnchor262Source.data
    WideAnchor262Source.path_swapped WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor262Cell034
