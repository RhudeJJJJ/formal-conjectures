/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor266Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor266Cell121
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (116269/8192)
  b := (558091/32768)
  s := [(3103086577933/18014398509481984),(-440843814003/4503599627370496),(116082096537/4503599627370496)]
  L := [(595874975983758146565/590295810358705651712),(-3018251069/824633720832),(1155477145/1099511627776),(-102927239/412316860416),(2606005/68719476736)]
  c := (1106801999393/1099511627776)
  R := (2643467569/800000000000)
  total := (11191714981417/1000000000000000)
  k := 0
  n := 32
  sFloor := (1804039708069/36028797018963968)
  nFloor := 30808111362227732039469989982006891450104201884999313809935765268393341998839393234727404060765985628487680
  eFloor := 30509142124457338739501122811749429887761336498243321507243358967610909929682854565297923491035198953357312
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=465076,width:=93015,den:=32768,localDen:=1770887431076116955136,lowerC:=1782629396452630069248,s:=[305045822957125632,-173346841167003648,45645337671892992],L:=[1787624927951274439695,-6481644816236019712,1861026205893918720,-442069125372575744,67156237489274880],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor266Source.source.poly i) 465076 93015 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor266Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 42) (CoreQuotient.fused G u 0 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 42 WideAnchor266Source.data
    WideAnchor266Source.path_checked WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 0) (CoreQuotient.fused G u 42 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 0 WideAnchor266Source.data
    WideAnchor266Source.path_swapped WideAnchor266Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor266Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor266Cell121
