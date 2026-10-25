/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor016Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor016Cell002
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1509949/281474976710656)
  b := (905969/140737488355328)
  s := [(549755813887/549755813888),(-1/4398046511104),(-1/2199023255552)]
  L := [(50521660007117993045096413/42535295865117307932921825928971026432),(430772441039/906694364710971881029632),(86154259957/1813388729421943762059264),(1/56668397794435742564352),(-1/113336795588871485128704)]
  c := (1435911940663/1208925819614629174706176)
  R := (-343236914784743/25000000000000)
  total := (-3657381/250000000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (966861510731/309485009821345068724781056)
  eFloor := (327700224475/154742504910672534362390528)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1509949,width:=301989,den:=281474976710656,localDen:=127605887595351923798765477786913079296,lowerC:=151564980021251544446926848,s:=[127605887595119810041399468985369493504,-29014219670751100192948224,-58028439341502200385896448],L:=[151564980021353979135289239,60625831404522479961505792,6062567078730094449000448,2251799813685248,-1125899906842624],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor016Source.source.poly i) 1509949 301989 281474976710656
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor016Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 25) (CoreQuotient.fused G u 9 25) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 25 WideAnchor016Source.data
    WideAnchor016Source.path_checked WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 25 9) (CoreQuotient.fused G u 25 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 25 9 WideAnchor016Source.data
    WideAnchor016Source.path_swapped WideAnchor016Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor016Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor016Cell002
