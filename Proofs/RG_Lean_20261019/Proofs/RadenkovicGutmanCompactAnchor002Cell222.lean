/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell222
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1509513/262144)
  b := (103779/16384)
  s := [(5255124470141/2251799813685248),(-1446446935419/2251799813685248),(107572730235/1125899906842624)]
  L := [(19822625563932919021357/18889465931478580854784),(-110417480585/13194139533312),(6624766643/6597069766656),(-80991607/824633720832),(2867725/412316860416)]
  c := (1145630996755/1099511627776)
  R := (2054473380611/100000000000000)
  total := (12818081487169/1000000000000000)
  k := 0
  n := 32
  sFloor := (502977874399/562949953421312)
  nFloor := 24831753139488904387289541709909721088
  eFloor := 23552597758206114270721954257985077248
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell222
