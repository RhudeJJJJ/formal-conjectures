/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor265Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor265Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (934719/2147483648)
  b := (560831/1073741824)
  s := [(4397200964987/4398046511104),(-21128813/274877906944),(-8429857/1099511627776)]
  L := [(16840474759419272373178225/158456325028528675187087900672),(574140018853/13510798882111488),(9554324049/2251799813685248),(-4387327/3377699720527872),(-18183/281474976710656)]
  c := (1914540321129/18014398509481984)
  R := (-91494490816763/20000000000000)
  total := (-78016678313/200000000000000)
  k := 14
  n := 32
  sFloor := (2198414592275/4398046511104)
  nFloor := (673664818787/36028797018963968)
  eFloor := (1218760435449/72057594037927936)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=934719,width:=186943,den:=2147483648,localDen:=475368975085586025561263702016,lowerC:=50521424278255981345898496,s:=[475277583057327327085747765248,-36539794311775062413279232,-3644611281022710460710912],L:=[50521424278257817119534675,20200756054412971470749696,2016977354383751651524608,-617461382573516128256,-30708357009179148288],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor265Source.source.poly i) 934719 186943 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor265Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 41) (CoreQuotient.fused G u 0 41) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 41 WideAnchor265Source.data
    WideAnchor265Source.path_checked WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 41 0) (CoreQuotient.fused G u 41 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 41 0 WideAnchor265Source.data
    WideAnchor265Source.path_swapped WideAnchor265Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor265Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor265Cell064
