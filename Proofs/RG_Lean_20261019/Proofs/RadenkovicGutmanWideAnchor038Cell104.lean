/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor038Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor038Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (670803/1048576)
  b := (1609927/2097152)
  s := [(2817622791021/17592186044416),(-515880749289/17592186044416),(25648019119/8796093022208)]
  L := [(594312443178087380047/590295810358705651712),(158252036997/2199023255552),(-11028122943/1099511627776),(84476379/137438953472),(-1149301/68719476736)]
  c := (1106993189413/1099511627776)
  R := (169534873663/50000000000000)
  total := (2474405956387/1000000000000000)
  k := 0
  n := 32
  sFloor := (1176519039985/17592186044416)
  nFloor := (507544202771/2048)
  eFloor := (1459702833051/8192)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1341606,width:=268321,den:=2097152,localDen:=590295810358705651712,lowerC:=594312443177946054656,s:=[94543732342964355072,-17310085522126798848,1721209426926370816],L:=[594312443178087380047,42480457714218565632,-5920678422056534016,362823285089501184,-9872420416520192],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor038Source.source.poly i) 1341606 268321 2097152
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor038Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 17) (CoreQuotient.fused G u 10 17) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 10 17 WideAnchor038Source.data
    WideAnchor038Source.path_checked WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 17 10) (CoreQuotient.fused G u 17 10) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 17 10 WideAnchor038Source.data
    WideAnchor038Source.path_swapped WideAnchor038Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor038Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor038Cell104
