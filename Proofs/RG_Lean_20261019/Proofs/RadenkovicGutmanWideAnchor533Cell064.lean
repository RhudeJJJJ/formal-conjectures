/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor533Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor533Cell064
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (934719/2147483648)
  b := (560831/1073741824)
  s := [(2156509855407/2199023255552),(-33059759659/4398046511104),(-1404100147/2199023255552)]
  L := [(467434620945609302867/37778931862957161709568),(2048664981679/422212465065984),(94448750611/211106232532992),(-47636311/6597069766656),(-3275917/13194139533312)]
  c := (1741329658573/140737488355328)
  R := (-219612368869961/100000000000000)
  total := (-183196657551/1000000000000000)
  k := 7
  n := 32
  sFloor := (1069287937715/2199023255552)
  nFloor := (1334662482273/144115188075855872)
  eFloor := (1052894291709/144115188075855872)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=934719,width:=186943,den:=2147483648,localDen:=113336795588871485128704,lowerC:=1402303862836102692864,s:=[111145671629697045233664,-851943519294150672384,-72366770540085510144],L:=[1402303862836827908601,549934318548234010624,50706786877788127232,-818385591388340224,-28139912758820864],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor533Source.source.poly i) 934719 186943 2147483648
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor533Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 11) (CoreQuotient.fused G u 5 11) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 11 WideAnchor533Source.data
    WideAnchor533Source.path_checked WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 11 5) (CoreQuotient.fused G u 11 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 11 5 WideAnchor533Source.data
    WideAnchor533Source.path_swapped WideAnchor533Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor533Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor533Cell064
