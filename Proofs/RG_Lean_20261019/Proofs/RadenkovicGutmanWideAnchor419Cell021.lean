/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor419Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor419Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (753743/4398046511104)
  b := (904491/4398046511104)
  s := [(4398046511101/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(5160722946921/19342813113834066795298816),(2064280962619/19342813113834066795298816),(309640911961/29014219670751100192948224),(1/1208925819614629174706176),(-1/1813388729421943762059264)]
  c := (645090368365/2417851639229258349412352)
  R := (-723806634385877/50000000000000)
  total := (-492972987/1000000000000000)
  k := 42
  n := 32
  sFloor := (1099511627775/2199023255552)
  nFloor := (1276770339449/2417851639229258349412352)
  eFloor := (321290701039/604462909807314587353088)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=753743,width:=150748,den:=4398046511104,localDen:=58028439341502200385896448,lowerC:=15482168840760,s:=[58028439341462617967296512,13194139533312,-26388279066624],L:=[15482168840763,6192842887857,619281823922,48,-32],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor419Source.source.poly i) 753743 150748 4398046511104
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor419Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 4 WideAnchor419Source.data
    WideAnchor419Source.path_checked WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 4 2 WideAnchor419Source.data
    WideAnchor419Source.path_swapped WideAnchor419Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor419Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor419Cell021
