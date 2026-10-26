/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor428Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor428Cell115
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1246027/262144)
  b := (23363/4096)
  s := [(4413029688825/1125899906842624),(-4577534832807/2251799813685248),(558051043077/1125899906842624)]
  L := [(314745432001135331269/295147905179352825856),(-67843536601/3298534883328),(14130983911/3298534883328),(-136013909/206158430208),(12742301/206158430208)]
  c := (1153956471513/1099511627776)
  R := (2416517062289/100000000000000)
  total := (1060793308379/40000000000000)
  k := 0
  n := 32
  sFloor := (1341156657749/1125899906842624)
  nFloor := 94800279580311552
  eFloor := 88203411569508352
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1246027,width:=249205,den:=262144,localDen:=885443715538058477568,lowerC:=929288494904229494784,s:=[3470547764242022400,-1799959936817037312,438869197909131264],L:=[944236296003405993807,-18211610684142125056,3793257109877948416,-584175290956120064,54727766070788096],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor428Source.source.poly i) 1246027 249205 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor428Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 6) (CoreQuotient.fused G u 2 6) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 2 6 WideAnchor428Source.data
    WideAnchor428Source.path_checked WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 2) (CoreQuotient.fused G u 6 2) (((13/7) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (13/7) 6 2 WideAnchor428Source.data
    WideAnchor428Source.path_swapped WideAnchor428Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor428Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor428Cell115
