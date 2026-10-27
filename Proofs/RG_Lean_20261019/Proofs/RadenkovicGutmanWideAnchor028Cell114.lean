/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor028Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor028Cell114
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (259589/65536)
  b := (1246027/262144)
  s := [(7209591713663/1125899906842624),(-452629316459/140737488355328),(26841222125/35184372088832)]
  L := [(1285930765065574560749/1180591620717411303424),(-339715113685/13194139533312),(10429350269/2199023255552),(-470421917/824633720832),(4087175/137438953472)]
  c := (586963450701/549755813888)
  R := (3274417421711/100000000000000)
  total := (14834348391143/500000000000000)
  k := 0
  n := 32
  sFloor := (1111869072497/562949953421312)
  nFloor := 407700046924598847588892166906607367512761336332428807281573888
  eFloor := 369539496619188026968054875481507346162335784965049914904018944
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1038356,width:=207671,den:=262144,localDen:=3541774862152233910272,lowerC:=3781483237062154911744,s:=[22679414522237681664,-11390789715247497216,2701925887770624000],L:=[3857792295196723682247,-91191581452124815360,16797644371456425984,-2020446748836626432,105325697748172800],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor028Source.source.poly i) 1038356 207671 262144
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor028Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 37) (CoreQuotient.fused G u 9 37) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 37 WideAnchor028Source.data
    WideAnchor028Source.path_checked WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 37 9) (CoreQuotient.fused G u 37 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 37 9 WideAnchor028Source.data
    WideAnchor028Source.path_swapped WideAnchor028Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor028Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor028Cell114
