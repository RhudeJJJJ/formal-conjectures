/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor259Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor259Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(2199013564849/2199023255552),(-1938117/1099511627776),(-193799/1099511627776)]
  L := [(670556793556980555682962019/324518553658426726783156020576256),(5717452737611/6917529027641081856),(95287382453/1152921504606846976),(-252341/432345564227567616),(-2105/72057594037927936)]
  c := (1191148146441/576460752303423488)
  R := (-654487243309553/100000000000000)
  total := (-27209903399/250000000000000)
  k := 19
  n := 32
  sFloor := (2199009301017/4398046511104)
  nFloor := (1192693099081/2305843009213693952)
  eFloor := (158978760611/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=973555660975280180349468061728768,lowerC:=2011670380670529225439051776,s:=[973551370689244932444516689903616,-1716093517627475282368659456,-171598106627560194894200832],L:=[2011670380670941667048886057,804659938081666307517841408,80463041270332638577557504,-568221416785149165568,-28440231646844682240],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor259Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor259Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 36) (CoreQuotient.fused G u 0 36) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 36 WideAnchor259Source.data
    WideAnchor259Source.path_checked WideAnchor259Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor259Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 36 0) (CoreQuotient.fused G u 36 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 36 0 WideAnchor259Source.data
    WideAnchor259Source.path_swapped WideAnchor259Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor259Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor259Cell055
