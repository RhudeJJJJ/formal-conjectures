/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor512Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor512Cell124
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1607301/65536)
  b := (241095/8192)
  s := [(303231657309/9007199254740992),(-2770912140795/144115188075855872),(366348256823/72057594037927936)]
  L := [(74025851545711593541/73786976294838206464),(-5599732115/4398046511104),(2455832825/6597069766656),(-24761087/274877906944),(5723083/412316860416)]
  c := (1101996736043/1099511627776)
  R := (11288212043/10000000000000)
  total := (1656320670639/250000000000000)
  k := 0
  n := 32
  sFloor := (1406745444897/144115188075855872)
  nFloor := 21615806709499681194634476203591730551294370246125806551839186163909819495042380729911877258806879567456414963800035934058759454899516211200
  eFloor := 21544603385478807097487433351082013595791921942645713587584587750203143052109292939203701574688890895489475329833483110858178032559426895872
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1607301,width:=321459,den:=65536,localDen:=221360928884514619392,lowerC:=221861247262660755456,s:=[7452221210025984,-4256121048261120,1125421844960256],L:=[222077554637134780623,-281843745706475520,82404075529830400,-19940261039702016,3072556789661696],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor512Source.source.poly i) 1607301 321459 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor512Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 42) (CoreQuotient.fused G u 4 42) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 4 42 WideAnchor512Source.data
    WideAnchor512Source.path_checked WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 42 4) (CoreQuotient.fused G u 42 4) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 42 4 WideAnchor512Source.data
    WideAnchor512Source.path_swapped WideAnchor512Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor512Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor512Cell124
