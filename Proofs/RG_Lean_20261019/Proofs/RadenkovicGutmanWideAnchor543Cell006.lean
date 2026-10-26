/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor543Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor543Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (195689/17592186044416)
  b := (939307/70368744177664)
  s := [(4398046511053/4398046511104),(-11/2199023255552)]
  L := [(2277468393717/302231454903657293676544),(85404955655/28334198897217871282176),(136647754487/453347182355485940514816),(-1/14167099448608935641088),(1/28334198897217871282176)]
  c := (569367098429/75557863725914323419136)
  R := (-1280569724765673/100000000000000)
  total := (-883769/31250000000000)
  k := 37
  n := 32
  sFloor := (2199023255515/4398046511104)
  nFloor := (1459249463585/154742504910672534362390528)
  eFloor := (1109969457209/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=782756,width:=156551,den:=70368744177664,localDen:=906694364710971881029632,lowerC:=6832405181148,s:=[906694364700457801089024,-4535485464576],L:=[6832405181151,2732958580960,273295508974,-64,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor543Source.source.poly i) 782756 156551 70368744177664
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
end Gebendorfer.RadenkovicGutman.WideAnchor543Cell006
