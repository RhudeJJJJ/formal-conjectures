/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor502Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor502Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(1615694863041/1125899906842624),(-7055635127935/9007199254740992),(898071092303/4503599627370496)]
  L := [(611909045641238177509/590295810358705651712),(-170896074403/13194139533312),(21769478561/6597069766656),(-562847735/824633720832),(37879171/412316860416)]
  c := (1128506870003/1099511627776)
  R := (1301464925869/100000000000000)
  total := (5237531011137/250000000000000)
  k := 0
  n := 32
  sFloor := (1916516490249/4503599627370496)
  nFloor := 70280440872231756360904220742483450237214431762044452074691177218048
  eFloor := 67603757295197485570902072372761061251588209713542665682850240528384
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=1770887431076116955136,lowerC:=1817587537490328158208,s:=[2541268285062119424,-1387194311233044480,353135922631016448],L:=[1835727136923714532527,-22937282830489616384,5843699904404258816,-1208706307226337280,162689800644591616],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor502Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor502Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 32) (CoreQuotient.fused G u 4 32) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 32 WideAnchor502Source.data
    WideAnchor502Source.path_checked WideAnchor502Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor502Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 32 4) (CoreQuotient.fused G u 32 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 32 4 WideAnchor502Source.data
    WideAnchor502Source.path_swapped WideAnchor502Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor502Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor502Cell117
