/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor040Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor040Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (562665/1099511627776)
  b := (337599/549755813888)
  s := [(4398046507163/4398046511104),(-1575/4398046511104),(-79/2199023255552)]
  L := [(557403617661/1180591620717411303424),(5351074723169/28334198897217871282176),(89184578277/4722366482869645213696),(-23/1770887431076116955136),(-1/295147905179352825856)]
  c := (557403617661/1180591620717411303424)
  R := (-1073687359849039/100000000000000)
  total := (-108930599/100000000000000)
  k := 31
  n := 32
  sFloor := (2199023252715/4398046511104)
  nFloor := (685020274687/37778931862957161709568)
  eFloor := (649921318549/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=562665,width:=112533,den:=1099511627776,localDen:=28334198897217871282176,lowerC:=13377686823864,s:=[28334198871828172111872,-10146860236800,-1017907249152],L:=[13377686823864,5351074723169,535107469662,-368,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor040Source.source.poly i) 562665 112533 1099511627776
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor040Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 19) (CoreQuotient.fused G u 10 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 19 WideAnchor040Source.data
    WideAnchor040Source.path_checked WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 10) (CoreQuotient.fused G u 19 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 10 WideAnchor040Source.data
    WideAnchor040Source.path_swapped WideAnchor040Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor040Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor040Cell027
