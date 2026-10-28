/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor513Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor513Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (260013/2097152)
  b := (624031/4194304)
  s := [(4418014680037/8796093022208),(-162291457143/4398046511104),(3878962169/2199023255552)]
  L := [(452305690671156369975/1180591620717411303424),(334781075795/6597069766656),(-389377295/1099511627776),(-46931413/206158430208),(1749427/68719476736)]
  c := (421242500349/1099511627776)
  R := (-47970635363457/100000000000000)
  total := (-1389132097651/125000000000000)
  k := 2
  n := 32
  sFloor := (2054473807213/8796093022208)
  nFloor := (335131801363/4294967296)
  eFloor := (144910206353/2147483648)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=520026,width:=104005,den:=4194304,localDen:=3541774862152233910272,lowerC:=1356917072013167689728,s:=[1778927677875639287808,-130694343909256986624,6247505871853584384],L:=[1356917072013469109925,179734221482402775040,-1254272060872458240,-806275535960276992,90164781020872704],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor513Source.source.poly i) 520026 104005 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor513Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 43) (CoreQuotient.fused G u 4 43) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 43 WideAnchor513Source.data
    WideAnchor513Source.path_checked WideAnchor513Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor513Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 43 4) (CoreQuotient.fused G u 43 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 43 4 WideAnchor513Source.data
    WideAnchor513Source.path_swapped WideAnchor513Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor513Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor513Cell095
