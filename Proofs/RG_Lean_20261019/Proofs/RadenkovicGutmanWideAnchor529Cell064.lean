/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor529Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor529Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (934719/2147483648)
  b := (560831/1073741824)
  s := [(1099503067377/1099511627776),(-3424109/1099511627776),(-171195/549755813888)]
  L := [(2893409274657/1152921504606846976),(289339617721/288230376151711744),(7233452331/72057594037927936),(-715/36028797018963968),(-9/9007199254740992)]
  c := (90419039833/36028797018963968)
  R := (-322384355775189/50000000000000)
  total := (-69140655687/125000000000000)
  k := 19
  n := 32
  sFloor := (549749650439/1099511627776)
  nFloor := (523177666849/144115188075855872)
  eFloor := (202882669085/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=934719,width:=186943,den:=2147483648,localDen:=1152921504606846976,lowerC:=2893409274656,s:=[1152912528377905152,-3590438518784,-359021936640],L:=[2893409274657,1157358470884,115735237296,-22880,-1152],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor529Source.source.poly i) 934719 186943 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor529Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 8) (CoreQuotient.fused G u 4 8) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 4 8 WideAnchor529Source.data
    WideAnchor529Source.path_checked WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 8 4) (CoreQuotient.fused G u 8 4) (((44/23) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (44/23) 8 4 WideAnchor529Source.data
    WideAnchor529Source.path_swapped WideAnchor529Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor529Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor529Cell064
