/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanWideAnchor270Source
namespace Gebendorfer.RadenkovicGutman.WideAnchor270Cell123
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def witness : ComputedPolynomialCell.Witness := {
  a := (669709/32768)
  b := (1607301/65536)
  s := [(523679152797/9007199254740992),(-2391846951733/72057594037927936),(316139992303/36028797018963968)]
  L := [(296517668217335907763/295147905179352825856),(-6005608871/3298534883328),(583754221/1099511627776),(-52841069/412316860416),(1354689/68719476736)]
  c := (275769260709/274877906944)
  R := (161873990443/100000000000000)
  total := (7913299214973/1000000000000000)
  k := 0
  n := 32
  sFloor := (151866640953/9007199254740992)
  nFloor := 280696180582080718748670396419477104729812284516499186853552951304145796772288108244507803454537931095756315818694678666512267476992
  eFloor := 279367013587938429635723511933856602615306697422669480047986814363680573329254382759431714970236393820046974347613922601444566892544
}
noncomputable def geometry : IntegerPolynomialPaymentCell.Geometry := {
 left:=1339418,width:=267883,den:=65536,localDen:=885443715538058477568,lowerC:=888314966990439579648,s:=[51479755436556288,-29391015342895104,7769456450838528],L:=[889553004652007723289,-1612118355844530176,470100991518179328,-113475331620339712,17455034853752832],transformed:=fun i => IntegerPolynomialPaymentCell.affine (WideAnchor270Source.source.poly i) 1339418 267883 65536
}
theorem checked : IntegerPolynomialPaymentCell.checks WideAnchor270Source.source witness geometry=true := by
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
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 46) (CoreQuotient.fused G u 0 46) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 0 46 WideAnchor270Source.data
    WideAnchor270Source.path_checked WideAnchor270Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor270Source.source_checked checked) budget logarithm_checked G u hd
theorem actual_integral_swapped {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 46 0) (CoreQuotient.fused G u 46 0) (((51/26) : ℚ) : ℝ) y :=
  SemanticPolynomialPaymentCell.actual_integral_lower (51/26) 46 0 WideAnchor270Source.data
    WideAnchor270Source.path_swapped WideAnchor270Source.norms_checked witness
    (IntegerPolynomialPaymentCell.conditions _ _ _ geometry WideAnchor270Source.source_checked checked) budget logarithm_checked G u hd
#print axioms checked
#print axioms budget
#print axioms logarithm_checked
#print axioms actual_integral
#print axioms actual_integral_swapped
end
end Gebendorfer.RadenkovicGutman.WideAnchor270Cell123
