/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor520Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor520Cell001
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1258291/281474976710656)
  b := (1509949/281474976710656)
  s := [(1099511627775/1099511627776),(1/4398046511104),(-1/2199023255552)]
  L := [(1746597712883/4835703278458516698824704),(698638529925/4835703278458516698824704),(17465949367/1208925819614629174706176)]
  c := (1746597712883/4835703278458516698824704)
  R := (-716234448961461/50000000000000)
  total := (-2544691/200000000000000)
  k := 42
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (671296300621/1237940039285380274899124224)
  eFloor := (642717518761/1237940039285380274899124224)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1258291,width:=251658,den:=281474976710656,localDen:=4835703278458516698824704,lowerC:=1746597712883,s:=[4835703278454118652313600,1099511627776,-2199023255552],L:=[1746597712883,698638529925,69863797468],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor520Source.source.poly i) 1258291 251658 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor520Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 5) (CoreQuotient.fused G u 4 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 5 WideAnchor520Source.data
    WideAnchor520Source.path_checked WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 4) (CoreQuotient.fused G u 5 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 4 WideAnchor520Source.data
    WideAnchor520Source.path_swapped WideAnchor520Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor520Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor520Cell001
