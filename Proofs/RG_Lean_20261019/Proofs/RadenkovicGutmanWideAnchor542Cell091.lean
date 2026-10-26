/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor542Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor542Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (501569/8388608)
  b := (1203765/16777216)
  s := [(770574797581/4398046511104),(114292306293/17592186044416),(5357625863/8796093022208)]
  L := [(222299612548102191793/295147905179352825856),(-21281573/12884901888),(-5558751743/3298534883328),(29589143/51539607552),(-18116215/206158430208)]
  c := (206249065101/274877906944)
  R := (-3590531649633/25000000000000)
  total := (-340964181179/200000000000000)
  k := 1
  n := 32
  sFloor := (770574797581/8796093022208)
  nFloor := (766568248957/2199023255552)
  eFloor := (1428601525049/4398046511104)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1003138,width:=200627,den:=16777216,localDen:=885443715538058477568,lowerC:=664374742079527452672,s:=[155137197878072573952,5752520129447460864,539316278104424448],L:=[666898837644306575379,-1462458560678985728,-1492166058922999808,508337606006669312,-77808550952304640],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor542Source.source.poly i) 1003138 200627 16777216
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor542Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 5 20) (CoreQuotient.fused G u 5 20) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 5 20 WideAnchor542Source.data
    WideAnchor542Source.path_checked WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 20 5) (CoreQuotient.fused G u 20 5) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 20 5 WideAnchor542Source.data
    WideAnchor542Source.path_swapped WideAnchor542Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor542Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor542Cell091
