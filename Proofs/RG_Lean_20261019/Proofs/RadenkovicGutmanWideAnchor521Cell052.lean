/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor521Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor521Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (838683/17179869184)
  b := (1006419/17179869184)
  s := [(2199023083905/2199023255552),(-34329/1099511627776),(-3433/1099511627776)]
  L := [(3511082269721/73786976294838206464),(2106641711809/110680464442257309696),(105331685941/55340232221128654848),(-577/6917529027641081856),(-13/3458764513820540928)]
  c := (438885283715/9223372036854775808)
  R := (-42151921180313/5000000000000)
  total := (-81395071219/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199023008381/4398046511104)
  nFloor := (1445497735401/18446744073709551616)
  eFloor := (592790879805/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=838683,width:=167736,den:=17179869184,localDen:=221360928884514619392,lowerC:=10533246809160,s:=[221360911605961850880,-6911340576768,-691154190336],L:=[10533246809163,4213283423618,421326743764,-18464,-832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor521Source.source.poly i) 838683 167736 17179869184
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor521Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 6 WideAnchor521Source.data
    WideAnchor521Source.path_checked WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 4 WideAnchor521Source.data
    WideAnchor521Source.path_swapped WideAnchor521Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor521Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor521Cell052
