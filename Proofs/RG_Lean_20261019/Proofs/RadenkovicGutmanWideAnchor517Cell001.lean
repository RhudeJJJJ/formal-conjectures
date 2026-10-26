/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor517Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor517Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1258291/281474976710656)
  b := (1509949/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(3857424757127/19807040628566084398385987584),(4628906029837/59421121885698253195157962752),(231445117525/29710560942849126597578981376),(5/3713820117856140824697372672),(-1/1856910058928070412348686336)]
  c := (1928712378563/9903520314283042199192993792)
  R := (-904370351431177/50000000000000)
  total := (-502737/31250000000000)
  k := 53
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (447857007521/1237940039285380274899124224)
  eFloor := (1086942867691/2475880078570760549798248448)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1258291,width:=251658,den:=281474976710656,localDen:=59421121885698253195157962752,lowerC:=11572274271378,s:=[59421121885684742396275851264],L:=[11572274271381,4628906029837,462890235050,80,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor517Source.source.poly i) 1258291 251658 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor517Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_checked WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_swapped WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor517Cell001
