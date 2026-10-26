/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor420Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor420Cell100
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (323497/1048576)
  b := (1552785/4194304)
  s := [(7309017131517/17592186044416),(-715823010165/8796093022208),(45587406135/4398046511104)]
  L := [(38148925643514233103/73786976294838206464),(274409880925/2199023255552),(-8797906127/1099511627776),(-199652385/274877906944),(1736561/8589934592)]
  c := (284231645193/549755813888)
  R := (-32984232355281/100000000000000)
  total := (-8519951619049/500000000000000)
  k := 1
  n := 32
  sFloor := (1514930183931/8796093022208)
  nFloor := (132416889061/17179869184)
  eFloor := (846130403105/137438953472)
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1293988,width:=258797,den:=4194304,localDen:=73786976294838206464,lowerC:=38148925643506581504,s:=[30656239790790279168,-6004758629654200320,764829759606620160],L:=[38148925643514233103,9207667689626009600,-590417485761609728,-53593779008962560,14916945405018112],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor420Source.source.poly i) 1293988 258797 4194304
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor420Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 2 4) (CoreQuotient.fused G u 2 4) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 2 4 WideAnchor420Source.data
    WideAnchor420Source.path_checked WideAnchor420Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor420Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 4 2) (CoreQuotient.fused G u 4 2) (((32/17) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (32/17) 4 2 WideAnchor420Source.data
    WideAnchor420Source.path_swapped WideAnchor420Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor420Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor420Cell100
