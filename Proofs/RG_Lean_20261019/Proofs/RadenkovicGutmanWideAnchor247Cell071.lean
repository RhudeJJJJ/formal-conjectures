/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor247Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor247Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (837315/536870912)
  b := (502389/268435456)
  s := [(4397941215731/4398046511104),(-5264617/549755813888),(-263189/274877906944)]
  L := [(3725035142641/144115188075855872),(744991930087/72057594037927936),(111739730677/108086391056891904),(-2359/140737488355328),(-5659/6755399441055744)]
  c := (232814696415/9007199254740992)
  R := (-264082297248389/50000000000000)
  total := (-809118071217/500000000000000)
  k := 16
  n := 32
  sFloor := (2198947443885/4398046511104)
  nFloor := (2185439849647/36028797018963968)
  eFloor := (1012145399293/36028797018963968)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=837315,width:=167463,den:=536870912,localDen:=432345564227567616,lowerC:=11175105427920,s:=[432335213271220224,-4140263276544,-413960503296],L:=[11175105427923,4469951580522,446958922708,-7246848,-362176],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor247Source.source.poly i) 837315 167463 536870912
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor247Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 2) (CoreQuotient.fused G u 0 2) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 2 WideAnchor247Source.data
    WideAnchor247Source.path_checked WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 0) (CoreQuotient.fused G u 2 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 2 0 WideAnchor247Source.data
    WideAnchor247Source.path_swapped WideAnchor247Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor247Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor247Cell071
