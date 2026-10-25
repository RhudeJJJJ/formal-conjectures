/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor249Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor249Cell027
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (562665/1099511627776)
  b := (337599/549755813888)
  s := [(4398046511093/4398046511104),(-3/4398046511104),(-1/2199023255552)]
  L := [(2629302077951/1208925819614629174706176),(1051720831177/1208925819614629174706176),(157758124669/1813388729421943762059264),(1/75557863725914323419136),(-1/113336795588871485128704)]
  c := (1314651038975/604462909807314587353088)
  R := (-671350872187373/50000000000000)
  total := (-682318641/500000000000000)
  k := 39
  n := 32
  sFloor := (274877906943/549755813888)
  nFloor := (782964985823/151115727451828646838272)
  eFloor := (857813556155/302231454903657293676544)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=562665,width:=112533,den:=1099511627776,localDen:=3626777458843887524118528,lowerC:=7887906233850,s:=[3626777458834816553189376,-2473901162496,-1649267441664],L:=[7887906233853,3155162493531,315516249338,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor249Source.source.poly i) 562665 112533 1099511627776
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor249Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 0 2 WideAnchor249Source.data
    WideAnchor249Source.path_checked WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((36/19) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (36/19) 2 0 WideAnchor249Source.data
    WideAnchor249Source.path_swapped WideAnchor249Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor249Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor249Cell027
