/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor418Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor418Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (260013/2097152)
  b := (624031/4194304)
  s := [(6932444936373/8796093022208),(-563547918533/8796093022208),(2925994791/4398046511104)]
  L := [(164409739658515803019/1180591620717411303424),(1740478301889/35184372088832),(144585749935/52776558133248),(-756884495/2199023255552),(20298365/3298534883328)]
  c := (1224948016245/8796093022208)
  R := (-616065387741/625000000000)
  total := (-4481326861897/200000000000000)
  k := 3
  n := 32
  sFloor := (1593687251855/4398046511104)
  nFloor := (467673611381/1099511627776)
  eFloor := (198957613617/549755813888)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520026,width:=104005,den:=4194304,localDen:=3541774862152233910272,lowerC:=493229218975532974080,s:=[2791371026535265861632,-226914363733885059072,2356322237927129088],L:=[493229218975547409057,175202282484629766144,9702985428725923840,-1219047807327928320,21795203459317760],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor418Source.source.poly i) 520026 104005 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor418Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 2 4 WideAnchor418Source.data
    WideAnchor418Source.path_checked WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((40/21) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (40/21) 4 2 WideAnchor418Source.data
    WideAnchor418Source.path_swapped WideAnchor418Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor418Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor418Cell095
