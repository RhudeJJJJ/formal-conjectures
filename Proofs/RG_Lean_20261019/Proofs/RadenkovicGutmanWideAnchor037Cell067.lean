/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor037Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor037Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (201899/268435456)
  b := (969115/1073741824)
  s := [(137429941603/137438953472),(-57670573/2199023255552),(-2882049/1099511627776)]
  L := [(2981753132333/144115188075855872),(298173440181/36028797018963968),(7454176331/9007199254740992),(-15057/4503599627370496),(-189/1125899906842624)]
  c := (745438283083/36028797018963968)
  R := (-67411604681319/12500000000000)
  total := (-797138482607/1000000000000000)
  k := 16
  n := 32
  sFloor := (2198815630977/4398046511104)
  nFloor := (745687034259/36028797018963968)
  eFloor := (1181636595293/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=807596,width:=161519,den:=1073741824,localDen:=144115188075855872,lowerC:=2981753132332,s:=[144105738446307328,-3779498672128,-377755926528],L:=[2981753132333,1192693760724,119266821296,-481824,-24192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor037Source.source.poly i) 807596 161519 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor037Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 16) (CoreQuotient.fused G u 10 16) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 16 WideAnchor037Source.data
    WideAnchor037Source.path_checked WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 16 10) (CoreQuotient.fused G u 16 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 16 10 WideAnchor037Source.data
    WideAnchor037Source.path_swapped WideAnchor037Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor037Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor037Cell067
