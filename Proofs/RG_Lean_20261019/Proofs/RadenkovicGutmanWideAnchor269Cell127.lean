/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor269Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(1890097106973/288230376151711744),(-4330998761823/1152921504606846976),(574063024175/576460752303423488)]
  L := [(4727555267395421880149/4722366482869645213696),(-1918069259/4398046511104),(283399711/2199023255552),(-8664813/274877906944),(673041/137438953472)]
  c := (1100352643433/1099511627776)
  R := (38230344889/100000000000000)
  total := (3883446432149/1000000000000000)
  k := 0
  n := 32
  sFloor := (2188757857209/1152921504606846976)
  nFloor := 6115791749816554380820921095585500120298097843331059166682880621064134143852069928905824870102611176482137258525499749245344504179893940426912058572341646458880
  eFloor := 6108999142988636348072873994302692650569986217132402717337768826922097209631771753215899546920042151693371180200343322092308876846700135495880925170200840503296
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=4722366482869645213696,lowerC:=4725978617611884167168,s:=[30967351000645632,-17739770928427008,4702724294041600],L:=[4727555267395421880149,-2059511184716988416,608596245220425728,-148860353843822592,23125512670937088],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor269Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor269Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 45) (CoreQuotient.fused G u 0 45) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 45 WideAnchor269Source.data
    WideAnchor269Source.path_checked WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 45 0) (CoreQuotient.fused G u 45 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 45 0 WideAnchor269Source.data
    WideAnchor269Source.path_swapped WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor269Cell127
