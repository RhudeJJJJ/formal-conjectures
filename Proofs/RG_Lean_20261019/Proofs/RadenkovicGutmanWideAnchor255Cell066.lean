/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor255Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor255Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (672997/1073741824)
  b := (201899/268435456)
  s := [(4397361913587/4398046511104),(-17108333/274877906944),(-6828769/1099511627776)]
  L := [(23658195588449884926855589/316912650057057350374175801344),(2151050447005/72057594037927936),(107423545081/36028797018963968),(-3214401/4503599627370496),(-79993/2251799813685248)]
  c := (1344812721325/18014398509481984)
  R := (-475133593580007/100000000000000)
  total := (-291929136493/500000000000000)
  k := 14
  n := 32
  sFloor := (2198530432591/4398046511104)
  nFloor := (945946710369/36028797018963968)
  eFloor := (15410756655/562949953421312)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=672997,width:=134599,den:=1073741824,localDen:=316912650057057350374175801344,lowerC:=23658195588446768280371200,s:=[316863319607097990905365266432,-19724565023674972145451008,-1968258657523148454363136],L:=[23658195588449884926855589,9460419913659039896043520,944907495307830622158848,-226193361653427339264,-11258013906007752704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor255Source.source.poly i) 672997 134599 1073741824
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
end Gebendorfer.RadenkovicGutman.WideAnchor255Cell066
