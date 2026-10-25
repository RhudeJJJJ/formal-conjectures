/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor238Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor238Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1123495/68719476736)
  b := (674097/34359738368)
  s := [(2199023189055/2199023255552),(-53199/4398046511104),(-2659/2199023255552)]
  L := [(84740791309324465739943655/5192296858534827628530496329220096),(5780347300781/885443715538058477568),(289017314201/442721857769029238784),(-1229/55340232221128654848),(-41/27670116110564327424)]
  c := (301059768437/18446744073709551616)
  R := (-17930844907617/2000000000000)
  total := (-5801731811/200000000000000)
  k := 26
  n := 32
  sFloor := (549755789949/1099511627776)
  nFloor := (246482530727/18446744073709551616)
  eFloor := (228346040969/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1123495,width:=224699,den:=68719476736,localDen:=15576890575604482885591488987660288,lowerC:=254222373927960189931094016,s:=[15576890104569676868517292324945920,-188418880891636691792560128,-18835158716925579934826496],L:=[254222373927973397219830965,101688945116677202977488896,10168892722962852827103232,-345932746377396224,-23080948090273792],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor238Source.source.poly i) 1123495 224699 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor238Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 20) (CoreQuotient.fused G u 0 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 20 WideAnchor238Source.data
    WideAnchor238Source.path_checked WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 0) (CoreQuotient.fused G u 20 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 0 WideAnchor238Source.data
    WideAnchor238Source.path_swapped WideAnchor238Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor238Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor238Cell046
