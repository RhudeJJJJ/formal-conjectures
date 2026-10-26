/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor278Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor278Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1045159/274877906944)
  b := (627095/137438953472)
  s := [(4398046509775/4398046511104),(-531/4398046511104),(-27/2199023255552)]
  L := [(4539915537837/18889465931478580854784),(5447877793889/56668397794435742564352),(272392846897/28334198897217871282176),(-5/3541774862152233910272),(-1/1770887431076116955136)]
  c := (1134978884459/4722366482869645213696)
  R := (-221489618376281/20000000000000)
  total := (-4175157121/500000000000000)
  k := 32
  n := 32
  sFloor := (2199023254595/4398046511104)
  nFloor := (1045887115651/2361183241434822606848)
  eFloor := (657272381683/2361183241434822606848)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1045159,width:=209031,den:=274877906944,localDen:=56668397794435742564352,lowerC:=13619746613508,s:=[56668397777311707955200,-6841882902528,-695784701952],L:=[13619746613511,5447877793889,544785693794,-80,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor278Source.source.poly i) 1045159 209031 274877906944
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor278Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 6 WideAnchor278Source.data
    WideAnchor278Source.path_checked WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 6 0 WideAnchor278Source.data
    WideAnchor278Source.path_swapped WideAnchor278Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor278Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor278Cell038
