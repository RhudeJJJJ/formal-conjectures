/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor545Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor545Cell019
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (523433/4398046511104)
  b := (1256239/8796093022208)
  s := [(1099511626303/1099511627776),(-589/1099511627776),(-59/1099511627776)]
  L := [(4169825923283/4722366482869645213696),(5003786321371/14167099448608935641088),(83396358557/2361183241434822606848),(-25/885443715538058477568),(-1/147573952589676412928)]
  c := (2084912961641/2361183241434822606848)
  R := (-1042385079723223/100000000000000)
  total := (-245887337/1000000000000000)
  k := 31
  n := 32
  sFloor := (1099511625655/2199023255552)
  nFloor := (43648163143/37778931862957161709568)
  eFloor := (1059408301579/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1046866,width:=209373,den:=8796093022208,localDen:=14167099448608935641088,lowerC:=12509477769846,s:=[14167099429629475160064,-7589207212032,-760209211392],L:=[12509477769849,5003786321371,500378151342,-400,-96],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor545Source.source.poly i) 1046866 209373 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor545Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 23) (CoreQuotient.fused G u 5 23) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 23 WideAnchor545Source.data
    WideAnchor545Source.path_checked WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 23 5) (CoreQuotient.fused G u 23 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 23 5 WideAnchor545Source.data
    WideAnchor545Source.path_swapped WideAnchor545Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor545Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor545Cell019
