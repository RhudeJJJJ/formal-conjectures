/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor370Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor370Cell018
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (872389/8796093022208)
  b := (523433/4398046511104)
  s := [(4398046511101/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(1050646689181813744866202203559/5575186299632655785383929568162090376495104),(4374175487801/58028439341502200385896448),(72902590585/9671406556917033397649408),(-35/3626777458843887524118528),(3/604462909807314587353088)]
  c := (227822684585/1208925819614629174706176)
  R := (-732498524516207/50000000000000)
  total := (-144366869/500000000000000)
  k := 43
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1027357282735/4835703278458516698824704)
  eFloor := (352676291729/1208925819614629174706176)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=872389,width:=174477,den:=8796093022208,localDen:=16725558898897967356151788704486271129485312,lowerC:=3151940067543711876535308779520,s:=[16725558898886558500749734639872800800636928,3802951800684688204490109616128,-7605903601369376408980219232256],L:=[3151940067545441234598606610677,1260770246202479434992340434944,126076446640492734718609981440,-161409010644958576640,83010348331692982272],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor370Source.source.poly i) 872389 174477 8796093022208
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor370Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 10) (CoreQuotient.fused G u 2 10) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 2 10 WideAnchor370Source.data
    WideAnchor370Source.path_checked WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 10 2) (CoreQuotient.fused G u 10 2) (((21/11) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (21/11) 10 2 WideAnchor370Source.data
    WideAnchor370Source.path_swapped WideAnchor370Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor370Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor370Cell018
