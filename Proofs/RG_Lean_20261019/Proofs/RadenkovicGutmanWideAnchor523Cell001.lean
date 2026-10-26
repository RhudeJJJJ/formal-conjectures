/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor523Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor523Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1258291/281474976710656)
  b := (1509949/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(124157440564074535901520139/696898287454081973172991196020261297061888),(1411505557975/19807040628566084398385987584),(70575221791/9903520314283042199192993792),(1/309485009821345068724781056),(-1/618970019642690137449562112)]
  c := (1764383349667/9903520314283042199192993792)
  R := (-906596635594167/50000000000000)
  total := (-16127393/1000000000000000)
  k := 53
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (176706492235/618970019642690137449562112)
  eFloor := (1265527740177/2475880078570760549798248448)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1258291,width:=251658,den:=281474976710656,localDen:=696898287454081973172991196020261297061888,lowerC:=124157440564047011683237888,s:=[696898287453923516847962667345074209161216],L:=[124157440564074535901520139,49662936757246828426035200,4966289727492776708276224,2251799813685248,-1125899906842624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor523Source.source.poly i) 1258291 251658 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor523Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 6) (CoreQuotient.fused G u 4 6) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 6 WideAnchor523Source.data
    WideAnchor523Source.path_checked WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 4) (CoreQuotient.fused G u 6 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 6 4 WideAnchor523Source.data
    WideAnchor523Source.path_swapped WideAnchor523Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor523Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor523Cell001
