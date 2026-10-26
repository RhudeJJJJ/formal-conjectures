/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor545Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(1615694857223/1125899906842624),(-881954380023/1125899906842624),(56129441833/281474976710656)]
  L := [(152977261315859449729/147573952589676412928),(-170896070411/13194139533312),(21769476283/6597069766656),(-562847551/824633720832),(37879145/412316860416)]
  c := (282126717357/274877906944)
  R := (1301464900393/100000000000000)
  total := (1047506183621/50000000000000)
  k := 0
  n := 32
  sFloor := (239564561133/562949953421312)
  nFloor := 2174474765019966760649106967651848923115165737423994880
  eFloor := 2091658254485132613693279733772863180800696224265011200
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=442721857769029238784,lowerC:=454396884141056458752,s:=[635317068977799168,-346798573495123968,88283978399219712],L:=[458931783947578349187,-5734320573673111552,1460924823227072512,-302176478022336512,40672422243860480],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor545Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor545Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 23) (CoreQuotient.fused G u 5 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 23 WideAnchor545Source.data
    WideAnchor545Source.path_checked WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 5) (CoreQuotient.fused G u 23 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 5 WideAnchor545Source.data
    WideAnchor545Source.path_swapped WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor545Cell117
