/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor479Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor479Cell096
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (624031/4194304)
  b := (748837/4194304)
  s := [(4810464726263/8796093022208),(-621980329/8589934592),(16406028723/2199023255552)]
  L := [(80317842608778753897/295147905179352825856),(546684694261/6597069766656),(-3028902883/6597069766656),(-763053377/824633720832),(48670711/412316860416)]
  c := (1196829119455/4398046511104)
  R := (-65074240427583/100000000000000)
  total := (-17315488320353/1000000000000000)
  k := 2
  n := 32
  sFloor := (2119590492129/8796093022208)
  nFloor := (519411805549/274877906944)
  eFloor := (1118196105383/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=624031,width:=124806,den:=4194304,localDen:=885443715538058477568,lowerC:=240953527826236047360,s:=[484237234637371342848,-64113244123447689216,6605939702111404032],L:=[240953527826336261691,73374777596086059008,-406532463288909824,-819322324829339648,104519556009033728],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor479Source.source.poly i) 624031 124806 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor479Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 10) (CoreQuotient.fused G u 4 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 4 10 WideAnchor479Source.data
    WideAnchor479Source.path_checked WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 4) (CoreQuotient.fused G u 10 4) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 4 WideAnchor479Source.data
    WideAnchor479Source.path_swapped WideAnchor479Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor479Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor479Cell096
