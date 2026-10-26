/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor277Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor277Cell083
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (466597/33554432)
  b := (139979/8388608)
  s := [(156548340917/549755813888),(-351019622303/8796093022208),(29252870289/4398046511104)]
  L := [(174785732734554413413/295147905179352825856),(462154578953/8796093022208),(-121983961175/13194139533312),(681908855/549755813888),(-98880097/824633720832)]
  c := (1302255188931/2199023255552)
  R := (-26195788240251/100000000000000)
  total := (-674780985467/1000000000000000)
  k := 1
  n := 32
  sFloor := (1106129786473/8796093022208)
  nFloor := (1044409509789/281474976710656)
  eFloor := (981825956257/281474976710656)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=466597,width:=93319,den:=33554432,localDen:=885443715538058477568,lowerC:=524357198203588706304,s:=[252138751680590118912,-35334792141695090688,5889380681502425088],L:=[524357198203663240239,46522003178901209088,-8186205060674355200,1098291086654177280,-106171695710076928],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor277Source.source.poly i) 466597 93319 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor277Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 5) (CoreQuotient.fused G u 0 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 5 WideAnchor277Source.data
    WideAnchor277Source.path_checked WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 0) (CoreQuotient.fused G u 5 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 0 WideAnchor277Source.data
    WideAnchor277Source.path_swapped WideAnchor277Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor277Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor277Cell083
