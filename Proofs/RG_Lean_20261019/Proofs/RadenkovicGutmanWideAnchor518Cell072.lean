/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor518Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor518Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (502389/268435456)
  b := (1205733/536870912)
  s := [(2198840123811/2199023255552),(-146491475/4398046511104),(-7320811/2199023255552)]
  L := [(4091137062093/144115188075855872),(4909420353869/432345564227567616),(245484387601/216172782113783808),(352357/27021597764222976),(8771/13510798882111488)]
  c := (1022784265523/36028797018963968)
  R := (-104695452342799/20000000000000)
  total := (-962165624873/500000000000000)
  k := 16
  n := 32
  sFloor := (1099379778631/2199023255552)
  nFloor := (116866040507/2251799813685248)
  eFloor := (342851409545/4503599627370496)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1004778,width:=200955,den:=536870912,localDen:=432345564227567616,lowerC:=12273411186276,s:=[432309559062233088,-14400697958400,-1439330009088],L:=[12273411186279,4909420353869,490968775202,5637712,280672],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor518Source.source.poly i) 1004778 200955 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor518Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_checked WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 4) (CoreQuotient.fused G u 4 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 4 WideAnchor518Source.data
    WideAnchor518Source.path_swapped WideAnchor518Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor518Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor518Cell072
