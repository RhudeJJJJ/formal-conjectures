/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor242Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor242Cell127
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1388707/32768)
  b := (104153/2048)
  s := [(1890097106973/288230376151711744),(-4330998761823/1152921504606846976),(574063024175/576460752303423488)]
  L := [(1181888816737133024323/1180591620717411303424),(-1918069259/4398046511104),(283399711/2199023255552),(-8664813/274877906944),(673041/137438953472)]
  c := (1100352643329/1099511627776)
  R := (38230340163/100000000000000)
  total := (970861507861/250000000000000)
  k := 0
  n := 32
  sFloor := (2188757857209/1152921504606846976)
  nFloor := 27261449998092736689000550520030988814622241386030074547312636035760835843981162266165772288
  eFloor := 27231171610775510413644172682748120058777601077854459834328330944785372143963438771559464960
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1388707,width:=277741,den:=32768,localDen:=1180591620717411303424,lowerC:=1181494654291301892096,s:=[7741837750161408,-4434942732106752,1175681073510400],L:=[1181888816737133024323,-514877796179247104,152149061305106432,-37215088460955648,5781378167734272],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor242Source.source.poly i) 1388707 277741 32768
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor242Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 24) (CoreQuotient.fused G u 0 24) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 24 WideAnchor242Source.data
    WideAnchor242Source.path_checked WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 24 0) (CoreQuotient.fused G u 24 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 24 0 WideAnchor242Source.data
    WideAnchor242Source.path_swapped WideAnchor242Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor242Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor242Cell127
