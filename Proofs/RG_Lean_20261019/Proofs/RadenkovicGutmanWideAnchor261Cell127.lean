/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor261Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor261Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(7560388427893/1152921504606846976),(-2165499380913/576460752303423488),(35878939011/36028797018963968)]
  L := [(4727555267294975313185/4722366482869645213696),(-1918069259/4398046511104),(283399711/2199023255552),(-8664813/274877906944),(673041/137438953472)]
  c := (550176321705/549755813888)
  R := (38230343843/100000000000000)
  total := (3883446342013/1000000000000000)
  k := 0
  n := 32
  sFloor := (2188757857209/1152921504606846976)
  nFloor := 100651003614573426352681564599601351685029964623314283279096538045305519732427120671705390635913470593500141206452082702314179715877830656
  eFloor := 100539213886864457392224395049809691474898419163084471152580327845981253203075915741885910187507026808937231200375650907980082609662197760
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=4722366482869645213696,lowerC:=4725978617513099919360,s:=[30967351000649728,-17739770928439296,4702724294049792],L:=[4727555267294975313185,-2059511184716988416,608596245220425728,-148860353843822592,23125512670937088],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor261Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor261Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 38) (CoreQuotient.fused G u 0 38) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 38 WideAnchor261Source.data
    WideAnchor261Source.path_checked WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 38 0) (CoreQuotient.fused G u 38 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 38 0 WideAnchor261Source.data
    WideAnchor261Source.path_swapped WideAnchor261Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor261Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor261Cell127
