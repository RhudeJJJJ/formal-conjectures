/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor505Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor505Cell113
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (865297/262144)
  b := (259589/65536)
  s := [(2860864678491/281474976710656),(-1370776770311/281474976710656),(78077756057/70368744177664)]
  L := [(20554372416437456257/18446744073709551616),(-190325340623/6597069766656),(3311453165/824633720832),(-14499379/103079215104),(-5573329/103079215104)]
  c := (149702042295/137438953472)
  R := (2136677253653/50000000000000)
  total := (15894934541251/500000000000000)
  k := 0
  n := 32
  sFloor := (225299866551/70368744177664)
  nFloor := 839251614855608519991307318401818134466103607296
  eFloor := 738038740235779281718483265088922303352937644032
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=865297,width:=173059,den:=262144,localDen:=55340232221128654848,lowerC:=60278003981384417280,s:=[562468882708758528,-269505679257305088,61402845851418624],L:=[61663117249312368771,-1596564674952822784,222227860092354560,-7784294827163648,-2992158223106048],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor505Source.source.poly i) 865297 173059 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor505Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 35) (CoreQuotient.fused G u 4 35) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 35 WideAnchor505Source.data
    WideAnchor505Source.path_checked WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 35 4) (CoreQuotient.fused G u 35 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 35 4 WideAnchor505Source.data
    WideAnchor505Source.path_swapped WideAnchor505Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor505Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor505Cell113
