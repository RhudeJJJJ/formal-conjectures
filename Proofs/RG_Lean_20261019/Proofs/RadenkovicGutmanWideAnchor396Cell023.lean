/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor396Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor396Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1085389/4398046511104)
  b := (651233/2199023255552)
  s := [(1099511627775/1099511627776),(-3/4398046511104),(1/2199023255552)]
  L := [(4938592928965/9671406556917033397649408),(1975429891459/9671406556917033397649408),(98771130603/4835703278458516698824704),(-5/604462909807314587353088),(1/302231454903657293676544)]
  c := (1234648232241/2417851639229258349412352)
  R := (-28303114412113/2000000000000)
  total := (-346930221/500000000000000)
  k := 41
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (687602529913/604462909807314587353088)
  eFloor := (1061806585955/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1085389,width:=217077,den:=4398046511104,localDen:=9671406556917033397649408,lowerC:=4938592928964,s:=[9671406556908237304627200,-6597069766656,4398046511104],L:=[4938592928965,1975429891459,197542261206,-80,32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor396Source.source.poly i) 1085389 217077 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor396Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_checked WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_swapped WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor396Cell023
