/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor031Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor031Cell020
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1256239/8796093022208)
  b := (753743/4398046511104)
  s := [(4398046511097/4398046511104),(-5/4398046511104),(1/2199023255552)]
  L := [(205618632934157188175111463/340282366920938463463374607431768211456),(584401443073/2417851639229258349412352),(21914984329/906694364710971881029632),(3/302231454903657293676544),(-1/226673591177742970257408)]
  c := (730504129841/1208925819614629174706176)
  R := (-175842335770189/12500000000000)
  total := (-399136163/1000000000000000)
  k := 41
  n := 32
  sFloor := (2199023255547/4398046511104)
  nFloor := (27898165061/37778931862957161709568)
  eFloor := (1141972701269/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1256239,width:=251247,den:=8796093022208,localDen:=1020847100762815390390123822295304634368,lowerC:=616855898802100505136857088,s:=[1020847100761190594088561760684499533824,-1160568786830044007717928960,464227514732017603087171584],L:=[616855898802471564525334389,246741573867969649764728832,24674078814478664829239296,10133099161583616,-4503599627370496],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor031Source.source.poly i) 1256239 251247 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor031Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_checked WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 10) (CoreQuotient.fused G u 10 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 10 WideAnchor031Source.data
    WideAnchor031Source.path_swapped WideAnchor031Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor031Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor031Cell020
