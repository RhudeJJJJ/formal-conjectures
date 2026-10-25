/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor014Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor014Cell060
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (901543/4294967296)
  b := (1081851/4294967296)
  s := [(2193781511759/2199023255552),(-2089383341/2199023255552),(-25613819/274877906944)]
  L := [(271151312014074359995343/154742504910672534362390528),(4723298556229/6755399441055744),(233849098447/3377699720527872),(-57551371/422212465065984),(-1381075/211106232532992)]
  c := (493221363311/281474976710656)
  R := (-317342037193157/100000000000000)
  total := (-129299934991/1000000000000000)
  k := 10
  n := 32
  sFloor := (1095743608933/2199023255552)
  nFloor := (649719080609/144115188075855872)
  eFloor := (221221547253/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=901543,width:=180308,den:=4294967296,localDen:=464227514732017603087171584,lowerC:=813453936041963242389504,s:=[463120949947974177603452928,-441081845435705717686272,-43257894638975748931584],L:=[813453936042223079986029,324582605251961153388544,32139975360926380457984,-63278401608950480896,-3037016042661478400],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor014Source.source.poly i) 901543 180308 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor014Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 23) (CoreQuotient.fused G u 9 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 23 WideAnchor014Source.data
    WideAnchor014Source.path_checked WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 9) (CoreQuotient.fused G u 23 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 9 WideAnchor014Source.data
    WideAnchor014Source.path_swapped WideAnchor014Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor014Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor014Cell060
