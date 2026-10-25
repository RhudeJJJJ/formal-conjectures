/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor500Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor500Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (78259/536870912)
  b := (375643/2147483648)
  s := [(4398014073027/4398046511104),(-6487479/2199023255552),(-324341/1099511627776)]
  L := [(110588585540373834185489849/40564819207303340847894502572032),(942920175199/864691128455135232),(31428997997/288230376151711744),(-236095/216172782113783808),(-123/2251799813685248)]
  c := (1571558322273/576460752303423488)
  R := (-64062974240273/10000000000000)
  total := (-36806879081/200000000000000)
  k := 19
  n := 32
  sFloor := (34359373443/68719476736)
  nFloor := (333186085763/288230376151711744)
  eFloor := (450705626963/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=313036,width:=62607,den:=2147483648,localDen:=121694457621910022543683507716096,lowerC:=331765756620922718640930816,s:=[121693560056553029117517074792448,-359018594389695504624648192,-35898212517666178084110336],L:=[331765756621121502556469547,132704217177073100125110272,13269714718867243608834048,-132909669253004656640,-6647313049998852096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor500Source.source.poly i) 313036 62607 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor500Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 30) (CoreQuotient.fused G u 4 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 30 WideAnchor500Source.data
    WideAnchor500Source.path_checked WideAnchor500Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor500Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 4) (CoreQuotient.fused G u 30 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 4 WideAnchor500Source.data
    WideAnchor500Source.path_swapped WideAnchor500Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor500Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor500Cell058
