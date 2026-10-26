/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor531Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor531Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(1615694857223/1125899906842624),(-881954380023/1125899906842624),(56129441833/281474976710656)]
  L := [(611909044135210343009/590295810358705651712),(-170896070411/13194139533312),(21769476283/6597069766656),(-562847551/824633720832),(37879145/412316860416)]
  c := (1128506867327/1099511627776)
  R := (260292961461/20000000000000)
  total := (20950122403643/1000000000000000)
  k := 0
  n := 32
  sFloor := (239564561133/562949953421312)
  nFloor := 4963227563913541957682009735168
  eFloor := 4774199300881962327028547977216
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=1770887431076116955136,lowerC:=1817587533180328476672,s:=[2541268275911196672,-1387194293980495872,353135913596878848],L:=[1835727132405631029027,-22937282294692446208,5843699292908290048,-1208705912089346048,162689688975441920],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor531Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor531Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 9) (CoreQuotient.fused G u 5 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 9 WideAnchor531Source.data
    WideAnchor531Source.path_checked WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 5) (CoreQuotient.fused G u 9 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 5 WideAnchor531Source.data
    WideAnchor531Source.path_swapped WideAnchor531Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor531Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor531Cell117
