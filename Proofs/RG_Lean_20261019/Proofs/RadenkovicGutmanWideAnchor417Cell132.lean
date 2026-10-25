/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor417Cell132
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (863885/8192)
  b := (518331/4096)
  s := [(245685543941/576460752303423488),(-1126843203975/4611686018427387904),(298921697585/4611686018427387904)]
  L := [(18892845821449592298889/18889465931478580854784),(-941517193/13194139533312),(46606125/2199023255552),(-4295279/824633720832),(111587/137438953472)]
  c := (1099648372219/1099511627776)
  R := (1243606133/20000000000000)
  total := (1573006132333/1000000000000000)
  k := 0
  n := 32
  sFloor := (568781422569/4611686018427387904)
  nFloor := 57959797956082891967408506395845373984768
  eFloor := 57949379630302192482738468082304954662912
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=863885,width:=172777,den:=8192,localDen:=56668397794435742564352,lowerC:=56675445549362879397888,s:=[24151871711576064,-13846649290444800,3673149819924480],L:=[56678537464348776896667,-4043785552556720128,1201030696009728000,-295169325315129344,46009201503240192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor417Source.source.poly i) 863885 172777 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor417Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 2 4 WideAnchor417Source.data
    WideAnchor417Source.path_checked WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 4 2 WideAnchor417Source.data
    WideAnchor417Source.path_swapped WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor417Cell132
