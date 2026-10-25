/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor253Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor253Cell097
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (748837/4194304)
  b := (224651/1048576)
  s := [(1106464500125/2199023255552),(-78246242445/2199023255552),(3948859763/2199023255552)]
  L := [(275133506329568037995/590295810358705651712),(1152298445877/17592186044416),(-47859192157/26388279066624),(213509249/1099511627776),(-68148911/1649267441664)]
  c := (1024952181911/2199023255552)
  R := (-38168366366061/100000000000000)
  total := (-6224474996267/500000000000000)
  k := 2
  n := 32
  sFloor := (1032167117443/4398046511104)
  nFloor := (28373393041/268435456)
  eFloor := (1287735559407/17179869184)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=748837,width:=149767,den:=4194304,localDen:=1770887431076116955136,lowerC:=825400518988422709248,s:=[891042907916599296000,-63012197313030389760,3180041913482870784],L:=[825400518988704113985,115994159537656430592,-3211776017613979648,343880715693195264,-73174336000753664],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor253Source.source.poly i) 748837 149767 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor253Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 30) (CoreQuotient.fused G u 0 30) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 30 WideAnchor253Source.data
    WideAnchor253Source.path_checked WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 30 0) (CoreQuotient.fused G u 30 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 30 0 WideAnchor253Source.data
    WideAnchor253Source.path_swapped WideAnchor253Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor253Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor253Cell097
