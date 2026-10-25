/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor503Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor503Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (650171/68719476736)
  b := (780205/68719476736)
  s := [(4398045982395/4398046511104),(-211481/4398046511104),(-10575/2199023255552)]
  L := [(83079214452947060643943765/1298074214633706907132624082305024),(472249830705/18446744073709551616),(5903108727/2305843009213693952),(-1013/2305843009213693952),(-13/576460752303423488)]
  c := (1180626646443/18446744073709551616)
  R := (-828217654304163/100000000000000)
  total := (-7747266197/500000000000000)
  k := 24
  n := 32
  sFloor := (1099511437441/2199023255552)
  nFloor := (572727702921/73786976294838206464)
  eFloor := (1075750741821/147573952589676412928)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=650171,width:=130034,den:=68719476736,localDen:=1298074214633706907132624082305024,lowerC:=83079214452880830105649152,s:=[1298074058586353107662170876805120,-62418174135234714964852736,-6242378194543312266854400],L:=[83079214452947060643943765,33231627524825278442373120,3323154782905590374989824,-570268302815789056,-29273397577908224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor503Source.source.poly i) 650171 130034 68719476736
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor503Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 33) (CoreQuotient.fused G u 4 33) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 33 WideAnchor503Source.data
    WideAnchor503Source.path_checked WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 33 4) (CoreQuotient.fused G u 33 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 33 4 WideAnchor503Source.data
    WideAnchor503Source.path_swapped WideAnchor503Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor503Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor503Cell043
