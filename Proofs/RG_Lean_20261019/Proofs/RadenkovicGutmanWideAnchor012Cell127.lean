/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor012Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor012Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(7556188364685/1152921504606846976),(-1081786848919/288230376151711744),(286696200369/288230376151711744)]
  L := [(147736011952202102771/147573952589676412928),(-359237201/824633720832),(141438433/1099511627776),(-12962879/412316860416),(335413/68719476736)]
  c := (550176159273/549755813888)
  R := (9553895507/25000000000000)
  total := (1940813843909/500000000000000)
  k := 0
  n := 32
  sFloor := (1093956442621/576460752303423488)
  nFloor := 921251743165514658404219226207962143483278638268445927702851357657762656747343085549176687615259745942446800896
  eFloor := 920229107673609800125070172088191506684674658768228849148219628142090476983183007113797549189777081322967138304
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=442721857769029238784,lowerC:=443060364584329150464,s:=[2901576332039040,-1661624599939584,440365363766784],L:=[443208035856606308313,-192864003725197312,56950635387420672,-13918785341751296,2160881798479872],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor012Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor012Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 21) (CoreQuotient.fused G u 9 21) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 21 WideAnchor012Source.data
    WideAnchor012Source.path_checked WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 21 9) (CoreQuotient.fused G u 21 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 21 9 WideAnchor012Source.data
    WideAnchor012Source.path_swapped WideAnchor012Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor012Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor012Cell127
