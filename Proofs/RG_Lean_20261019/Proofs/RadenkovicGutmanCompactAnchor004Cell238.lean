/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell238
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (867017/32768)
  b := (476859/16384)
  s := [(1933726689011/72057594037927936),(-2280694005971/288230376151711744),(181496510327/144115188075855872)]
  L := [(37884262958921017954797/37778931862957161709568),(-7247514149/13194139533312),(533827217/6597069766656),(-8523001/824633720832),(403363/412316860416)]
  c := (551025944729/549755813888)
  R := (115384488771/100000000000000)
  total := (3353421854623/1000000000000000)
  k := 0
  n := 32
  sFloor := (1454301442681/144115188075855872)
  nFloor := 202875034582322438091431962227019645013948126569152291129006377656375050240
  eFloor := 202300115031626803056974780615972817757590338968389203288820487963948351488
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell238
