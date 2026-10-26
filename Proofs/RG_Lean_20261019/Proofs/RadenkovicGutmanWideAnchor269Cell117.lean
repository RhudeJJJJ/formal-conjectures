/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor269Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor269Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(3296267044071/2251799813685248),(-3641368481001/4503599627370496),(468143624827/2251799813685248)]
  L := [(306177385538907883067/295147905179352825856),(-59422237923/4398046511104),(7810193767/2199023255552),(-210033015/274877906944),(14673829/137438953472)]
  c := (1128926439931/1099511627776)
  R := (1320051075501/100000000000000)
  total := (21309815373391/1000000000000000)
  k := 0
  n := 32
  sFloor := (1943726428397/4503599627370496)
  nFloor := 111004570172913005805617057406240383644796944083922187343535945803163456182088105984
  eFloor := 106693006229211645680580646144375089326278492543139571165040071266199911236592730112
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=295147905179352825856,lowerC:=303043883693334593536,s:=[432048314000474112,-238640724770881536,61360521193324544],L:=[306177385538907883067,-3987758883350249472,1048266462646501376,-225521232626319360,31511807831048192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor269Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor269Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 45) (CoreQuotient.fused G u 0 45) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 45 WideAnchor269Source.data
    WideAnchor269Source.path_checked WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 45 0) (CoreQuotient.fused G u 45 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 45 0 WideAnchor269Source.data
    WideAnchor269Source.path_swapped WideAnchor269Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor269Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor269Cell117
