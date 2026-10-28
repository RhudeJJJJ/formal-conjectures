/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor271Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor271Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (897139/131072)
  b := (538283/65536)
  s := [(3296267044071/2251799813685248),(-3641368481001/4503599627370496),(468143624827/2251799813685248)]
  L := [(306177385564097005279/295147905179352825856),(-59422237911/4398046511104),(7810193729/2199023255552),(-210033007/274877906944),(14673827/137438953472)]
  c := (1128926440025/1099511627776)
  R := (82503192479/6250000000000)
  total := (21309815429991/1000000000000000)
  k := 0
  n := 32
  sFloor := (1943726428397/4503599627370496)
  nFloor := 264673759211176733565004269151171715764921845378878574983956094536235641247619446996992
  eFloor := 254393481243478509546439687698711335863678017799510480743951758512851381115129906069504
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=897139,width:=179427,den:=131072,localDen:=295147905179352825856,lowerC:=303043883718567526400,s:=[432048314000474112,-238640724770881536,61360521193324544],L:=[306177385564097005279,-3987758882544943104,1048266457546227712,-225521224036384768,31511803536080896],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor271Source.source.poly i) 897139 179427 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor271Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 47) (CoreQuotient.fused G u 0 47) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 47 WideAnchor271Source.data
    WideAnchor271Source.path_checked WideAnchor271Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor271Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 47 0) (CoreQuotient.fused G u 47 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 47 0 WideAnchor271Source.data
    WideAnchor271Source.path_swapped WideAnchor271Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor271Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor271Cell117
