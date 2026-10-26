/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor427Cell129
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (249967/4096)
  b := (1199841/16384)
  s := [(39584239421/18014398509481984),(-1451751777667/1152921504606846976),(96240110243/288230376151711744)]
  L := [(9449757797183393617811/9444732965739290427392),(-2792442695/13194139533312),(137852913/2199023255552),(-12671779/824633720832),(328587/137438953472)]
  c := (549959275517/549755813888)
  R := (9250651977/50000000000000)
  total := (2707376723309/1000000000000000)
  k := 0
  n := 32
  sFloor := (1466599986249/2305843009213693952)
  nFloor := 14333906347375697974998344330560977758060544
  eFloor := 14326221417705743625037014671588797571923968
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=999868,width:=199973,den:=16384,localDen:=28334198897217871282176,lowerC:=28344685229728421904384,s:=[62260625152671744,-35678251687944192,9460787797327872],L:=[28349273391550180853433,-5996725025489551360,1776221258979999744,-435399011097116672,67740980106756096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor427Source.source.poly i) 999868 199973 16384
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor427Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 2 6 WideAnchor427Source.data
    WideAnchor427Source.path_checked WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 2 WideAnchor427Source.data
    WideAnchor427Source.path_swapped WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor427Cell129
