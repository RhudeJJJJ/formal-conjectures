/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor255Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor255Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (904491/4398046511104)
  b := (1085389/4398046511104)
  s := [(2199023255515/2199023255552),(-31/4398046511104),(-1/2199023255552)]
  L := [(4859638432351/604462909807314587353088),(1943853223751/604462909807314587353088),(97192553747/302231454903657293676544),(-5/37778931862957161709568),(1/18889465931478580854784)]
  c := (1214909608087/151115727451828646838272)
  R := (-638666052744963/50000000000000)
  total := (-260764891/500000000000000)
  k := 37
  n := 32
  sFloor := (1099511627749/2199023255552)
  nFloor := (213555854133/75557863725914323419136)
  eFloor := (445337063013/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=904491,width:=180898,den:=4398046511104,localDen:=604462909807314587353088,lowerC:=4859638432348,s:=[604462909797144104796160,-4260607557632,-274877906944],L:=[4859638432351,1943853223751,194385107494,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor255Source.source.poly i) 904491 180898 4398046511104
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
end Gebendorfer.RadenkovicGutman.WideAnchor255Cell022
