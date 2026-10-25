/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor257Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor257Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(2279808002043/4503599627370496),(-2566593350803/9007199254740992),(83810352529/1125899906842624)]
  L := [(37594780769235496813/36893488147419103232),(-31614663529/4398046511104),(4406627791/2199023255552),(-126745347/274877906944),(9382721/137438953472)]
  c := (278569876243/274877906944)
  R := (8338691059/1250000000000)
  total := (7812612945687/500000000000000)
  k := 0
  n := 32
  sFloor := (1331752736757/9007199254740992)
  nFloor := 14372200411825403719307638042638109531636546604737004645709577831388354183168
  eFloor := 14089828519152391760334415350148430660736422341288477668721889215629697744896
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=36893488147419103232,lowerC:=37389015878576635904,s:=[18676187152736256,-10512766364889088,2746297631670272],L:=[37594780769235496813,-265203019396677632,73930946281209856,-17011472508911616,2518654990155776],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor257Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor257Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 34) (CoreQuotient.fused G u 0 34) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 34 WideAnchor257Source.data
    WideAnchor257Source.path_checked WideAnchor257Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor257Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 34 0) (CoreQuotient.fused G u 34 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 34 0 WideAnchor257Source.data
    WideAnchor257Source.path_swapped WideAnchor257Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor257Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor257Cell119
