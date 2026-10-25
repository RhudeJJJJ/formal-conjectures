/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor262Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor262Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1620475/2199023255552)
  b := (972285/1099511627776)
  s := [(2199023149605/2199023255552),(-84755/4398046511104),(-4239/2199023255552)]
  L := [(933719356231/36893488147419103232),(2240926345369/221360928884514619392),(56023147675/55340232221128654848),(-547/13835058055282163712),(-7/3458764513820540928)]
  c := (933719356231/36893488147419103232)
  R := (-174921249815003/20000000000000)
  total := (-1275192019/1000000000000000)
  k := 26
  n := 32
  sFloor := (549755775747/1099511627776)
  nFloor := (603358249073/75557863725914323419136)
  eFloor := (1148592738565/151115727451828646838272)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1620475,width:=324095,den:=2199023255552,localDen:=221360928884514619392,lowerC:=5602316137386,s:=[221360918219540398080,-4265858826240,-426711711744],L:=[5602316137386,2240926345369,224092590700,-8752,-448],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor262Source.source.poly i) 1620475 324095 2199023255552
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor262Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 3) (CoreQuotient.fused G u 0 3) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 3 WideAnchor262Source.data
    WideAnchor262Source.path_checked WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 3 0) (CoreQuotient.fused G u 3 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 3 0 WideAnchor262Source.data
    WideAnchor262Source.path_swapped WideAnchor262Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor262Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor262Cell029
