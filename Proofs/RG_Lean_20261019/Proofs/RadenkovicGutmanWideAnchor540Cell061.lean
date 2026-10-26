/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor540Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor540Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1081851/4294967296)
  b := (1298221/4294967296)
  s := [(4387474555995/4398046511104),(-4213863399/4398046511104),(-206583453/2199023255552)]
  L := [(48140532145349548164239/38685626227668133590597632),(838556019523/1688849860263936),(166046192309/3377699720527872),(-41385229/422212465065984),(-992639/211106232532992)]
  c := (1401073885655/1125899906842624)
  R := (-167227472707661/50000000000000)
  total := (-16378142991/100000000000000)
  k := 10
  n := 32
  sFloor := (2191423762845/4398046511104)
  nFloor := (1017956792517/288230376151711744)
  eFloor := (984364346405/288230376151711744)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1081851,width:=216370,den:=4294967296,localDen:=116056878683004400771792896,lowerC:=144421596436028844933120,s:=[115777902981308287423610880,-111196603321444756094976,-10902763616621605945344],L:=[144421596436048644492717,57625130875443560316928,5705303724739853811712,-11375885125918130176,-545709061341970432],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor540Source.source.poly i) 1081851 216370 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor540Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 18) (CoreQuotient.fused G u 5 18) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 18 WideAnchor540Source.data
    WideAnchor540Source.path_checked WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 18 5) (CoreQuotient.fused G u 18 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 18 5 WideAnchor540Source.data
    WideAnchor540Source.path_swapped WideAnchor540Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor540Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor540Cell061
