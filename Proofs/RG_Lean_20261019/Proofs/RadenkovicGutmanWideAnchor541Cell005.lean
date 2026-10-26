/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor541Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor541Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (652297/70368744177664)
  b := (195689/17592186044416)
  s := [(4398046511069/4398046511104),(-13/4398046511104),(-1/2199023255552)]
  L := [(109889944185940044609896341/21267647932558653966460912964485513216),(7495801168295/3626777458843887524118528),(374788909055/1813388729421943762059264),(43/226673591177742970257408),(-11/113336795588871485128704)]
  c := (12200234621/2361183241434822606848)
  R := (-81214777500081/6250000000000)
  total := (-597923/25000000000000)
  k := 38
  n := 32
  sFloor := (2199023255527/4398046511104)
  nFloor := (941614771519/154742504910672534362390528)
  eFloor := (719071323419/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=652297,width:=130459,den:=70368744177664,localDen:=63802943797675961899382738893456539648,lowerC:=329669832557809346958852096,s:=[63802943797168213055144594640079945728,-188592427859882151254163456,-29014219670751100192948224],L:=[329669832557820133829689023,131867528704596447560990720,13186712430958536829173760,12103423998558208,-6192449487634432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor541Source.source.poly i) 652297 130459 70368744177664
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor541Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 19) (CoreQuotient.fused G u 5 19) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 19 WideAnchor541Source.data
    WideAnchor541Source.path_checked WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 19 5) (CoreQuotient.fused G u 19 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 19 5 WideAnchor541Source.data
    WideAnchor541Source.path_swapped WideAnchor541Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor541Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor541Cell005
