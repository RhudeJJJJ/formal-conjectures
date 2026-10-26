/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor043Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor043Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1671897/33554432)
  b := (501569/8388608)
  s := [(3256874818465/4398046511104),(-539799619875/8796093022208),(15441664473/4398046511104)]
  L := [(128655741447211721025/1180591620717411303424),(1339326541075/35184372088832),(93796434877/52776558133248),(-748945327/2199023255552),(30870083/3298534883328)]
  c := (958559970909/8796093022208)
  R := (-55415769978607/50000000000000)
  total := (-10243396122929/1000000000000000)
  k := 4
  n := 32
  sFloor := (375302084125/1099511627776)
  nFloor := (56922043891/274877906944)
  eFloor := (622947180313/2199023255552)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1671897,width:=334379,den:=33554432,localDen:=3541774862152233910272,lowerC:=385967224341456224256,s:=[2622782031088708485120,-217352035664658432000,12435270732626264064],L:=[385967224341635163075,134821024044888883200,6294572191845449728,-1206260882233884672,33146499227451392],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor043Source.source.poly i) 1671897 334379 33554432
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor043Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 22) (CoreQuotient.fused G u 10 22) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 22 WideAnchor043Source.data
    WideAnchor043Source.path_checked WideAnchor043Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor043Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 22 10) (CoreQuotient.fused G u 22 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 22 10 WideAnchor043Source.data
    WideAnchor043Source.path_swapped WideAnchor043Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor043Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor043Cell090
