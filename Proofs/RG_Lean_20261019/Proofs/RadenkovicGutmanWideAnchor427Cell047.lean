/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor427Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor427Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (674097/34359738368)
  b := (202229/8589934592)
  s := [(274877903927/274877906944),(-19309/4398046511104),(-965/2199023255552)]
  L := [(129062176603/36893488147419103232),(2477986434575/1770887431076116955136),(41299651081/295147905179352825856),(-11/110680464442257309696),(-1/18446744073709551616)]
  c := (129062176603/36893488147419103232)
  R := (-194710066220373/20000000000000)
  total := (-4728986603/125000000000000)
  k := 29
  n := 32
  sFloor := (549755805199/1099511627776)
  nFloor := (780675908851/147573952589676412928)
  eFloor := (1224674160539/147573952589676412928)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=674097,width:=134819,den:=34359738368,localDen:=1770887431076116955136,lowerC:=6194984476944,s:=[1770887411639242457088,-7774830329856,-777120645120],L:=[6194984476944,2477986434575,247797906486,-176,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor427Source.source.poly i) 674097 134819 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor427Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 2 6 WideAnchor427Source.data
    WideAnchor427Source.path_checked WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 2 WideAnchor427Source.data
    WideAnchor427Source.path_swapped WideAnchor427Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor427Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor427Cell047
