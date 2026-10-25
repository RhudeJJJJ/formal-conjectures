/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor017Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor017Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (1291879/131072)
  b := (775127/65536)
  s := [(4514528162821/9007199254740992),(-5052337376119/18014398509481984),(656633773315/9007199254740992)]
  L := [(4698469140071885421/4611686018427387904),(-46458152315/6597069766656),(6383549395/3298534883328),(-180574633/412316860416),(13175669/206158430208)]
  c := (278543974655/274877906944)
  R := (662446039691/100000000000000)
  total := (15493907213433/1000000000000000)
  k := 0
  n := 32
  sFloor := (661248312019/4503599627370496)
  nFloor := 1424537485640321573281746074590609002475486878992038155181244416823823582625792
  eFloor := 1396824570460762316526873786137503546478110237520186276821615187073587396739072
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1291879,width:=258375,den:=131072,localDen:=13835058055282163712,lowerC:=14019577284856381440,s:=[6934315258093056,-3880195104859392,1008589475811840],L:=[14095407420215656263,-97429807043706880,26774546761646080,-6059079243923456,884204179030016],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor017Source.source.poly i) 1291879 258375 131072
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor017Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 26) (CoreQuotient.fused G u 9 26) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 9 26 WideAnchor017Source.data
    WideAnchor017Source.path_checked WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 26 9) (CoreQuotient.fused G u 26 9) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 26 9 WideAnchor017Source.data
    WideAnchor017Source.path_swapped WideAnchor017Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor017Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor017Cell119
