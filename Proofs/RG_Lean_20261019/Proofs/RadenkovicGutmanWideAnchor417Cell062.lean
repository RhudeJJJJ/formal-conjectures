/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor417Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor417Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1298221/4294967296)
  b := (1557865/4294967296)
  s := [(1099509745921/1099511627776),(-188185/274877906944),(-75273/1099511627776)]
  L := [(2506000174895/2305843009213693952),(187949677201/432345564227567616),(75179507147/1729382256910270464),(-3823/108086391056891904),(-191/108086391056891904)]
  c := (1253000087447/1152921504606846976)
  R := (-686613448598207/100000000000000)
  total := (-102353142401/250000000000000)
  k := 20
  n := 32
  sFloor := (274877229477/549755813888)
  nFloor := (311600665805/144115188075855872)
  eFloor := (981439844731/576460752303423488)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1298221,width:=259644,den:=4294967296,localDen:=6917529027641081856,lowerC:=7518000524682,s:=[6917517188033150976,-4735830589440,-473576767488],L:=[7518000524685,3007194835216,300718028588,-244672,-12224],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor417Source.source.poly i) 1298221 259644 4294967296
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor417Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 2 4 WideAnchor417Source.data
    WideAnchor417Source.path_checked WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((52/27) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (52/27) 4 2 WideAnchor417Source.data
    WideAnchor417Source.path_swapped WideAnchor417Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor417Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor417Cell062
