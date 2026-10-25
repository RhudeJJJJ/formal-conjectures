/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor255Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor255Cell125
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (241095/8192)
  b := (144657/4096)
  s := [(1408363958981/72057594037927936),(-1611799816641/144115188075855872),(213443617711/72057594037927936)]
  L := [(1183263064024404941253/1180591620717411303424),(-11799152521/13194139533312),(1734977087/6597069766656),(-52796963/824633720832),(4086841/412316860416)]
  c := (34413937677/34359738368)
  R := (39404117489/50000000000000)
  total := (1111004590747/200000000000000)
  k := 0
  n := 32
  sFloor := (1631815336743/288230376151711744)
  nFloor := 12317680542098291345134577914215814971794283269845967475843364438870858158638703097820529493499384816467968
  eFloor := 12289390510344679722594605093659062832931389479325141784602917313295619559752766890742339122270177639530496
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=241095,width:=48219,den:=8192,localDen:=3541774862152233910272,lowerC:=3547361684383133073408,s:=[69223905311834112,-39611592293769216,10491180697731072],L:=[3549789192073214823759,-3167310887388184576,931458730996793344,-226761229413122048,35105696877903872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor255Source.source.poly i) 241095 48219 8192
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor255Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 32) (CoreQuotient.fused G u 0 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 32 WideAnchor255Source.data
    WideAnchor255Source.path_checked WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 0) (CoreQuotient.fused G u 32 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 0 WideAnchor255Source.data
    WideAnchor255Source.path_swapped WideAnchor255Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor255Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor255Cell125
