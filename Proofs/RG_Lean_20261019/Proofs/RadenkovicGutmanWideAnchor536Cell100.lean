/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor536Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor536Cell100
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (323497/1048576)
  b := (1552785/4194304)
  s := [(4031623044703/17592186044416),(-183572539243/17592186044416),(-3053396289/2199023255552)]
  L := [(116357173797550412713/147573952589676412928),(363414334421/8796093022208),(29465305643/13194139533312),(-370764539/549755813888),(42320257/824633720832)]
  c := (1733857002817/2199023255552)
  R := (-2376648787283/20000000000000)
  total := (-6515601312959/1000000000000000)
  k := 1
  n := 32
  sFloor := (955905833787/8796093022208)
  nFloor := (118704977445/268435456)
  eFloor := (377651301009/1073741824)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1293988,width:=258797,den:=4194304,localDen:=442721857769029238784,lowerC:=349071521392481009664,s:=[101459115977339830272,-4619754213822431232,-614729868889817088],L:=[349071521392651238139,18291242358232055808,988691594557259776,-298579044285284352,22720514971664384],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor536Source.source.poly i) 1293988 258797 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor536Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 14) (CoreQuotient.fused G u 5 14) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 14 WideAnchor536Source.data
    WideAnchor536Source.path_checked WideAnchor536Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor536Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 14 5) (CoreQuotient.fused G u 14 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 14 5 WideAnchor536Source.data
    WideAnchor536Source.path_swapped WideAnchor536Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor536Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor536Cell100
