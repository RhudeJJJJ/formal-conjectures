/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor543Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor543Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (650171/68719476736)
  b := (780205/68719476736)
  s := [(4398010037319/4398046511104),(-3647329/1099511627776),(-91177/274877906944)]
  L := [(3455261349818543175716057/633825300114114700748351602688),(314251059537/144115188075855872),(981999973/4503599627370496),(-26459/18014398509481984),(-331/4503599627370496)]
  c := (785635472725/144115188075855872)
  R := (-605981527263863/100000000000000)
  total := (-5644642409/500000000000000)
  k := 18
  n := 32
  sFloor := (2198996994585/4398046511104)
  nFloor := (503386924149/73786976294838206464)
  eFloor := (382898281545/73786976294838206464)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=650171,width:=130034,den:=68719476736,localDen:=633825300114114700748351602688,lowerC:=3455261349817728001638400,s:=[633820043687729587417585287168,-2102542019238093287063552,-210239848051076973461504],L:=[3455261349818543175716057,1382090776007438235598848,138204209765019910406144,-930943301098405888,-46584108645613568],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor543Source.source.poly i) 650171 130034 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor543Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 21) (CoreQuotient.fused G u 5 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 21 WideAnchor543Source.data
    WideAnchor543Source.path_checked WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 5) (CoreQuotient.fused G u 21 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 5 WideAnchor543Source.data
    WideAnchor543Source.path_swapped WideAnchor543Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor543Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor543Cell043
