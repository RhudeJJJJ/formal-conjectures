/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1324989/70368744177664)
  b := (1457487/70368744177664)
  s := [(1099511627771/1099511627776),(-1/1099511627776)]
  L := [(797827143677246334986709823/340282366920938463463374607431768211456),(3401318584351/7253554917687775048237056),(28344128989/1208925819614629174706176),(11/453347182355485940514816),(-1/75557863725914323419136)]
  c := (708612851665/302231454903657293676544)
  R := (-267789049177633/20000000000000)
  total := (-6279997/250000000000000)
  k := 39
  n := 32
  sFloor := (549755813885/1099511627776)
  nFloor := (329467837151/19342813113834066795298816)
  eFloor := (157356674221/9671406556917033397649408)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell017
