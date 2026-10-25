/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor497Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor497Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1620475/2199023255552)
  b := (972285/1099511627776)
  s := [(17179869167/17179869184),(-869/2199023255552),(-11/274877906944)]
  L := [(2508339713815/4722366482869645213696),(3010007651729/14167099448608935641088),(150500381743/7083549724304467820544),(-47/885443715538058477568),(5/442721857769029238784)]
  c := (1254169856907/2361183241434822606848)
  R := (-213559548187107/20000000000000)
  total := (-1559920233/1000000000000000)
  k := 31
  n := 32
  sFloor := (2199023252419/4398046511104)
  nFloor := (766982088331/18889465931478580854784)
  eFloor := (44643480137/1180591620717411303424)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1620475,width:=324095,den:=2199023255552,localDen:=14167099448608935641088,lowerC:=7525019141442,s:=[14167099434590162386944,-5598489870336,-566935683072],L:=[7525019141445,3010007651729,301000763486,-752,160],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor497Source.source.poly i) 1620475 324095 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor497Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 27) (CoreQuotient.fused G u 4 27) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 27 WideAnchor497Source.data
    WideAnchor497Source.path_checked WideAnchor497Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor497Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 27 4) (CoreQuotient.fused G u 27 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 27 4 WideAnchor497Source.data
    WideAnchor497Source.path_swapped WideAnchor497Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor497Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor497Cell029
