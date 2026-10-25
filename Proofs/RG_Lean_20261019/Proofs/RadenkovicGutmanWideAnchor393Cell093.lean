/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor393Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor393Cell093
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (722259/8388608)
  b := (433355/4194304)
  s := [(1999870619655/2199023255552),(-71440324253/2199023255552),(-1718379767/1099511627776)]
  L := [(1408676051337971255257/18889465931478580854784),(1472256900377/52776558133248),(9124661575/4398046511104),(-404082917/3298534883328),(-164509/274877906944)]
  c := (1311931806931/17592186044416)
  R := (-64898852899063/50000000000000)
  total := (-20853410986863/1000000000000000)
  k := 4
  n := 32
  sFloor := (481248383967/1099511627776)
  nFloor := (103769128449/549755813888)
  eFloor := (263990233807/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=722259,width:=144451,den:=8388608,localDen:=56668397794435742564352,lowerC:=4226028154013123346432,s:=[51536273445896878817280,-1841003137693623779328,-88564618816477200384],L:=[4226028154013913765771,1580823809607386267648,117570369155078553600,-6942091653549129728,-33914917195087872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor393Source.source.poly i) 722259 144451 8388608
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor393Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_checked WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((56/29) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (56/29) 2 2 WideAnchor393Source.data
    WideAnchor393Source.path_swapped WideAnchor393Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor393Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor393Cell093
