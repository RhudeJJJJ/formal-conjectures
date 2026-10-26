/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor264Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor264Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (748837/4194304)
  b := (224651/1048576)
  s := [(4415470179961/8796093022208),(-37782807955/1099511627776),(1505854389/1099511627776)]
  L := [(138123336815429327323/295147905179352825856),(840272286437/13194139533312),(-1617991631/1649267441664),(-922231/25769803776),(-1572035/206158430208)]
  c := (1029099053259/2199023255552)
  R := (-37966478656981/100000000000000)
  total := (-620266302761/50000000000000)
  k := 2
  n := 32
  sFloor := (515656818929/2199023255552)
  nFloor := (1352131828735/2147483648)
  eFloor := (958017244681/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=748837,width:=149767,den:=4194304,localDen:=885443715538058477568,lowerC:=414370010446121926656,s:=[444475781704587411456,-30426735847082557440,1212674128742449152],L:=[414370010446287981969,56389718593469677568,-868652642543337472,-31687615874859008,-6751838913167360],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor264Source.source.poly i) 748837 149767 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor264Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 40) (CoreQuotient.fused G u 0 40) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 40 WideAnchor264Source.data
    WideAnchor264Source.path_checked WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 40 0) (CoreQuotient.fused G u 40 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 40 0 WideAnchor264Source.data
    WideAnchor264Source.path_swapped WideAnchor264Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor264Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor264Cell097
