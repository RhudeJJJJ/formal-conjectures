/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor242Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor242Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (518331/4096)
  b := 128
  s := [(4550556842977/18446744073709551616),(-156840209079/18446744073709551616),(1751850149/9223372036854775808)]
  L := [(309523502978153663538306861/309485009821345068724781056),(-1568301/549755813888),(53955/1099511627776),(-13/17179869184),(1/68719476736)]
  c := (1099645299477/1099511627776)
  R := (6078315717/100000000000000)
  total := (17882685237/200000000000000)
  k := 0
  n := 32
  sFloor := (1099305083549/9223372036854775808)
  nFloor := 10675611523210693570234745971442376191337591567518389816764906852913897332022099161247351276279425482756688540382265344
  eFloor := 10674278609693465179514354219971881835768165703761822631200238704418124942941885974591697361136626975554942812184117248
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=518331,width:=5957,den:=4096,localDen:=309485009821345068724781056,lowerC:=309522635060270917497126912,s:=[76345675074903212032,-2631342065203544064,58782336698810368],L:=[309523502978153663538306861,-882874974900597030912,15186982368423444480,-234187180623265792,4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor242Source.source.poly i) 518331 5957 4096
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor242Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 24) (CoreQuotient.fused G u 0 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 24 WideAnchor242Source.data
    WideAnchor242Source.path_checked WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 0) (CoreQuotient.fused G u 24 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 0 WideAnchor242Source.data
    WideAnchor242Source.path_swapped WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor242Cell133
