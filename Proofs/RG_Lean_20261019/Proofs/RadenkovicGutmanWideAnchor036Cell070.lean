/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor036Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor036Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1395525/1073741824)
  b := (837315/536870912)
  s := [(4360329415757/4398046511104),(-14872419095/4398046511104),(-685809963/2199023255552)]
  L := [(21970191976794375898611/4835703278458516698824704),(2024532970557/1125899906842624),(290879468155/1688849860263936),(-104245855/70368744177664),(-6567751/105553116266496)]
  c := (1278833484789/281474976710656)
  R := (-134852380713717/50000000000000)
  total := (-169246516797/250000000000000)
  k := 8
  n := 32
  sFloor := (135752668023/274877906944)
  nFloor := (1855607203147/18014398509481984)
  eFloor := (1758840670799/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1395525,width:=279105,den:=1073741824,localDen:=14507109835375550096474112,lowerC:=65910575930381621526528,s:=[14382698680675662399799296,-49057193184330944348160,-4524336172578769993728],L:=[65910575930383127695833,26085908694648137711616,2498635605607196917760,-21491161822490787840,-902664824104681472],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor036Source.source.poly i) 1395525 279105 1073741824
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor036Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 15) (CoreQuotient.fused G u 10 15) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 15 WideAnchor036Source.data
    WideAnchor036Source.path_checked WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 15 10) (CoreQuotient.fused G u 15 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 15 10 WideAnchor036Source.data
    WideAnchor036Source.path_swapped WideAnchor036Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor036Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor036Cell070
