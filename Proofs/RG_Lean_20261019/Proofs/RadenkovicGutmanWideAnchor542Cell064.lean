/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor542Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor542Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (934719/2147483648)
  b := (560831/1073741824)
  s := [(4365441097501/4398046511104),(-6450199279/2199023255552),(-151642027/549755813888)]
  L := [(37270418068446559801519/9671406556917033397649408),(5166769010485/3377699720527872),(250448054207/1688849860263936),(-193775455/211106232532992),(-4244315/105553116266496)]
  c := (2169423857031/562949953421312)
  R := (-55587291028811/20000000000000)
  total := (-233860066817/1000000000000000)
  k := 9
  n := 32
  sFloor := (2175663781363/4398046511104)
  nFloor := (817119288451/72057594037927936)
  eFloor := (197225735025/18014398509481984)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=934719,width:=186943,den:=2147483648,localDen:=29014219670751100192948224,lowerC:=111811254205323895898112,s:=[28799119482441434614726656,-85104829304794458882048,-8003144253409062813696],L:=[111811254205339679404557,44382207852038712197120,4302664808663600857088,-26632295743760629760,-1166668423611023360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor542Source.source.poly i) 934719 186943 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor542Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 20) (CoreQuotient.fused G u 5 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 20 WideAnchor542Source.data
    WideAnchor542Source.path_checked WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 5) (CoreQuotient.fused G u 20 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 5 WideAnchor542Source.data
    WideAnchor542Source.path_swapped WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor542Cell064
