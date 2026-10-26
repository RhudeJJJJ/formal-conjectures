/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor515Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor515Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1246027/262144)
  b := (23363/4096)
  s := [(555934656111/140737488355328),(-4632138175649/2251799813685248),(566565984451/1125899906842624)]
  L := [(2520988871842559007069/2361183241434822606848),(-141341155345/6597069766656),(7628441051/1649267441664),(-311973257/412316860416),(8006233/103079215104)]
  c := (1154709162627/1099511627776)
  R := (1224559963659/50000000000000)
  total := (1347216120787/50000000000000)
  k := 0
  n := 32
  sFloor := (1348987072757/1125899906842624)
  nFloor := 94974923105107968
  eFloor := 88254453926985728
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1246027,width:=249205,den:=262144,localDen:=7083549724304467820544,lowerC:=7439157134811765669888,s:=[27981107422379900928,-14571446759007977472,3564524962270150656],L:=[7562966615527677021207,-151763909946407649280,32763904833508868096,-5359659744166412288,550184142386495488],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor515Source.source.poly i) 1246027 249205 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor515Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_checked WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 4 WideAnchor515Source.data
    WideAnchor515Source.path_swapped WideAnchor515Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor515Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor515Cell115
