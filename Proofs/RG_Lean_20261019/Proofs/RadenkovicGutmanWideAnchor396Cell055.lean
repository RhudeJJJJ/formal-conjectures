/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor396Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor396Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (724621/8589934592)
  b := (869545/8589934592)
  s := [(4398046105901/4398046511104),(-162083/4398046511104),(-8103/2199023255552)]
  L := [(154893791543780339747321733/2596148429267413814265248164610048),(5282808064129/221360928884514619392),(88046663013/36893488147419103232),(-1255/13835058055282163712),(-9/2305843009213693952)]
  c := (1100586583957/18446744073709551616)
  R := (-6653822057637/800000000000)
  total := (-138742508141/1000000000000000)
  k := 24
  n := 32
  sFloor := (1099511481903/2199023255552)
  nFloor := (612940757677/4611686018427387904)
  eFloor := (946512698889/9223372036854775808)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=724621,width:=144924,den:=8589934592,localDen:=7788445287802241442795744493830144,lowerC:=464681374631035529160818688,s:=[7788444570233341708459925921857536,-287030747491110264439308288,-28699001708019551374934016],L:=[464681374631341019241965199,185872284602196997940707328,18587199315776364028624896,-706502191543746560,-30399297484750848],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor396Source.source.poly i) 724621 144924 8589934592
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor396Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_checked WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 2) (CoreQuotient.fused G u 2 2) (((17/9) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (17/9) 2 2 WideAnchor396Source.data
    WideAnchor396Source.path_swapped WideAnchor396Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor396Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor396Cell055
