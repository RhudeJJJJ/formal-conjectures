/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor248Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor248Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (868127/268435456)
  b := (130219/33554432)
  s := [(2198808816671/2199023255552),(-171531423/4398046511104),(-8571199/2199023255552)]
  L := [(3435821767527/36028797018963968),(515333535071/13510798882111488),(51517819087/13510798882111488),(-770657/3377699720527872),(-4811/422212465065984)]
  c := (1717910883763/18014398509481984)
  R := (-57861360526087/12500000000000)
  total := (-2933373312023/1000000000000000)
  k := 14
  n := 32
  sFloor := (137419654985/274877906944)
  nFloor := (511031322047/2251799813685248)
  eFloor := (261295267267/2251799813685248)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=868127,width:=173625,den:=268435456,localDen:=108086391056891904,lowerC:=10307465302578,s:=[108075850957012992,-4215556251648,-421291573248],L:=[10307465302581,4122668280568,412142552696,-24661024,-1231616],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor248Source.source.poly i) 868127 173625 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor248Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 0 2 WideAnchor248Source.data
    WideAnchor248Source.path_checked WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((48/25) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (48/25) 2 0 WideAnchor248Source.data
    WideAnchor248Source.path_swapped WideAnchor248Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor248Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor248Cell075
