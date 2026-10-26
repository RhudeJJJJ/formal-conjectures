/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor026Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor026Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (501569/8388608)
  b := (1203765/16777216)
  s := [(1771915914877/8796093022208),(304483914267/17592186044416),(-6687766737/8796093022208)]
  L := [(31629535786687487739/36893488147419103232),(-734684622839/13194139533312),(16883504197/3298534883328),(371662589/824633720832),(-32276983/206158430208)]
  c := (1774722289719/2199023255552)
  R := (-10718466641939/100000000000000)
  total := (-138235998349/125000000000000)
  k := 1
  n := 32
  sFloor := (1771915914877/17592186044416)
  nFloor := (182137607601/137438953472)
  eFloor := (8825488743/8589934592)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1003138,width:=200627,den:=16777216,localDen:=110680464442257309696,lowerC:=89324697583890726912,s:=[22295862028296781824,1915647149318602752,-84151580328198144],L:=[94888607360062463217,-6162981304624218112,566516393499951104,49883708278177792,-17328573299818496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor026Source.source.poly i) 1003138 200627 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor026Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 35) (CoreQuotient.fused G u 9 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 35 WideAnchor026Source.data
    WideAnchor026Source.path_checked WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 9) (CoreQuotient.fused G u 35 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 9 WideAnchor026Source.data
    WideAnchor026Source.path_swapped WideAnchor026Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor026Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor026Cell091
