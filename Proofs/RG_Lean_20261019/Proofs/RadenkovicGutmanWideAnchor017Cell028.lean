/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor017Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor017Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (337599/549755813888)
  b := (1620475/2199023255552)
  s := [(4398046482013/4398046511104),(-2909/1099511627776),(-291/1099511627776)]
  L := [(72929341090907767162611581/20769187434139310514121985316880384),(829109996751/590295810358705651712),(124366403815/885443715538058477568),(-23/36893488147419103232),(-7/55340232221128654848)]
  c := (518194135359/147573952589676412928)
  R := (-60835141593241/6250000000000)
  total := (-236789849/200000000000000)
  k := 29
  n := 32
  sFloor := (1099511617303/2199023255552)
  nFloor := (1172406225885/37778931862957161709568)
  eFloor := (1104216316969/37778931862957161709568)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1350396,width:=270079,den:=2199023255552,localDen:=62307562302417931542365955950641152,lowerC:=218788023272659571762528256,s:=[62307561890282841482883409215750144,-164848369184013575119699968,-16490503758180801086226432],L:=[218788023272723301487834743,87515143884772423810154496,8751507654353791127388160,-38843546786070528,-7881299347898368],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor017Source.source.poly i) 1350396 270079 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor017Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 26) (CoreQuotient.fused G u 9 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 26 WideAnchor017Source.data
    WideAnchor017Source.path_checked WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 9) (CoreQuotient.fused G u 26 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 9 WideAnchor017Source.data
    WideAnchor017Source.path_swapped WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor017Cell028
