/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor517Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor517Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1612557/67108864)
  b := (483767/16777216)
  s := [(4338923540597/4398046511104),(-23294807511/4398046511104),(-1069169585/2199023255552)]
  L := [(54340455237470166621815/9671406556917033397649408),(59217172657/26388279066624),(11769214897/52776558133248),(-3940739/13194139533312),(-137183/6597069766656)]
  c := (1581515396173/281474976710656)
  R := (-259083002603081/100000000000000)
  total := (-12001295875629/1000000000000000)
  k := 8
  n := 32
  sFloor := (1078372598479/2199023255552)
  nFloor := (1503599586533/140737488355328)
  eFloor := (1810897896395/140737488355328)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1612557,width:=322511,den:=67108864,localDen:=29014219670751100192948224,lowerC:=163021365712404445396992,s:=[28624181309504476132933632,-153677470350889206153216,-14106772689263284715520],L:=[163021365712410499865445,65109969900390508920832,6470194314523009089536,-8665776705060732928,-603337214532780032],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor517Source.source.poly i) 1612557 322511 67108864
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor517Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_checked WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((19/10) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (19/10) 4 4 WideAnchor517Source.data
    WideAnchor517Source.path_swapped WideAnchor517Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor517Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor517Cell086
