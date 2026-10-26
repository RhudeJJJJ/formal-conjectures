/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor533Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (868127/268435456)
  b := (130219/33554432)
  s := [(77216154207/137438953472),(-664679934583/8796093022208),(32654733751/4398046511104)]
  L := [(104957884881219899171/295147905179352825856),(2079215732759/26388279066624),(-15508914503/3298534883328),(-198800561/1649267441664),(3169523/51539607552)]
  c := (390998590295/1099511627776)
  R := (-51695871542809/100000000000000)
  total := (-75543813421/250000000000000)
  k := 2
  n := 32
  sFloor := (2171231701083/8796093022208)
  nFloor := (287996244287/562949953421312)
  eFloor := (113605959369/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=868127,width:=173625,den:=268435456,localDen:=885443715538058477568,lowerC:=314873654643586498560,s:=[497461285562936721408,-66908873000189165568,6574266258756206592],L:=[314873654643659697513,69766902918192037888,-4163142536677818368,-106730238490181632,54451990515679232],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor533Source.source.poly i) 868127 173625 268435456
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor533Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 11) (CoreQuotient.fused G u 5 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 11 WideAnchor533Source.data
    WideAnchor533Source.path_checked WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 5) (CoreQuotient.fused G u 11 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 5 WideAnchor533Source.data
    WideAnchor533Source.path_swapped WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor533Cell075
