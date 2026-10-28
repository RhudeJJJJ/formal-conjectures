/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor272Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor272Cell056
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (869545/8589934592)
  b := (521727/4294967296)
  s := [(4397914958193/4398046511104),(-26308727/2199023255552),(-1314921/1099511627776)]
  L := [(137171050244993696274983197/10141204801825835211973625643008),(4678093619641/864691128455135232),(77950277419/144115188075855872),(-1346029/54043195528445952),(-11211/9007199254740992)]
  c := (1949317866163/144115188075855872)
  R := (-70068054230221/12500000000000)
  total := (-55794217383/500000000000000)
  k := 17
  n := 32
  sFloor := (2198928540527/4398046511104)
  nFloor := (1080708136661/1152921504606846976)
  eFloor := (1194958037709/1152921504606846976)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=869545,width:=173909,den:=8589934592,localDen:=30423614405477505635920876929024,lowerC:=411513150734922055937949696,s:=[30422704384396992452139530846208,-363982765405569353068314624,-36384016746219355980693504],L:=[411513150734981088824949591,164595786579839862871949312,16455789390826649470107648,-757746962853735170048,-37867391566837972992],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor272Source.source.poly i) 869545 173909 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor272Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 48) (CoreQuotient.fused G u 0 48) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 48 WideAnchor272Source.data
    WideAnchor272Source.path_checked WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 48 0) (CoreQuotient.fused G u 48 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 48 0 WideAnchor272Source.data
    WideAnchor272Source.path_swapped WideAnchor272Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor272Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor272Cell056
