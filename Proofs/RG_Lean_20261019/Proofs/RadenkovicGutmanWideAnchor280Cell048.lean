/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor280Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor280Cell048
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (202229/8589934592)
  b := (970699/34359738368)
  s := [(4398046452273/4398046511104),(-11767/2199023255552),(-147/274877906944)]
  L := [(35032739275606856482613481/5192296858534827628530496329220096),(796551276587/295147905179352825856),(119482539079/442721857769029238784),(-33/18446744073709551616),(-7/27670116110564327424)]
  c := (497845168121/73786976294838206464)
  R := (-94070794793573/10000000000000)
  total := (-43851941549/1000000000000000)
  k := 28
  n := 32
  sFloor := (2199023213193/4398046511104)
  nFloor := (1471729363099/147573952589676412928)
  eFloor := (182363508411/18446744073709551616)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=808916,width:=161783,den:=34359738368,localDen:=15576890575604482885591488987660288,lowerC:=105098217826778321919148032,s:=[15576890367238325970313415812448256,-83352129605890672844341248,-8330254475782054156959744],L:=[105098217826820569447840443,42039234754906712048664576,4203918113073946299465728,-27866022694354944,-3940649673949184],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor280Source.source.poly i) 808916 161783 34359738368
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor280Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 6) (CoreQuotient.fused G u 0 6) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 0 6 WideAnchor280Source.data
    WideAnchor280Source.path_checked WideAnchor280Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor280Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 6 0) (CoreQuotient.fused G u 6 0) (((28/15) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (28/15) 6 0 WideAnchor280Source.data
    WideAnchor280Source.path_swapped WideAnchor280Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor280Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor280Cell048
