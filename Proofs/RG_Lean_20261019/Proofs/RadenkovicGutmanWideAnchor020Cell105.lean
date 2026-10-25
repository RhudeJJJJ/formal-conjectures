/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor020Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor020Cell105
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1609927/2097152)
  b := (241489/262144)
  s := [(4702903382031/35184372088832),(-246747651447/8796093022208),(13544109721/4398046511104)]
  L := [(157812996996401425267/147573952589676412928),(848294519447/13194139533312),(-77802511769/6597069766656),(724349857/824633720832),(-3125911/412316860416)]
  c := (1175798453363/1099511627776)
  R := (3354067256233/100000000000000)
  total := (715656164199/100000000000000)
  k := 0
  n := 32
  sFloor := (1912132827005/35184372088832)
  nFloor := 47408196485760
  eFloor := 33878320888480
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1609927,width:=321985,den:=2097152,localDen:=442721857769029238784,lowerC:=473438990988887457792,s:=[59176219400598454272,-12419215937457094656,1363394725901500416],L:=[473438990989204275801,28464040768757039104,-5221238181164220416,388882368334659584,-3356421378801664],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor020Source.source.poly i) 1609927 321985 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor020Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 29) (CoreQuotient.fused G u 9 29) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 29 WideAnchor020Source.data
    WideAnchor020Source.path_checked WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 29 9) (CoreQuotient.fused G u 29 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 29 9 WideAnchor020Source.data
    WideAnchor020Source.path_swapped WideAnchor020Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor020Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor020Cell105
