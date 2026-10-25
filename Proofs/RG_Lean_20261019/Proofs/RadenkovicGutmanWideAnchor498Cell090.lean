/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor498Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor498Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1671897/33554432)
  b := (501569/8388608)
  s := [(6365821710343/8796093022208),(-212225802363/4398046511104),(2275464161/549755813888)]
  L := [(84259100962172685761/590295810358705651712),(3774815526857/105553116266496),(-10528588281/17592186044416),(-532430147/6597069766656),(14603885/1099511627776)]
  c := (627779222743/4398046511104)
  R := (-97336359902759/100000000000000)
  total := (-9128614998973/1000000000000000)
  k := 3
  n := 32
  sFloor := (186805547881/549755813888)
  nFloor := (554750453085/2199023255552)
  eFloor := (622947180313/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1671897,width:=334379,den:=33554432,localDen:=1770887431076116955136,lowerC:=252777302886514163712,s:=[1281609190222967341056,-85453395048416673792,7329783116036308992],L:=[252777302886518057283,63330895454233690112,-1059842398592434176,-142923129298092032,23521203176079360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor498Source.source.poly i) 1671897 334379 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor498Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 28) (CoreQuotient.fused G u 4 28) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 28 WideAnchor498Source.data
    WideAnchor498Source.path_checked WideAnchor498Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor498Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 28 4) (CoreQuotient.fused G u 28 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 28 4 WideAnchor498Source.data
    WideAnchor498Source.path_swapped WideAnchor498Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor498Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor498Cell090
