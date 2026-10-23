/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (271413/1099511627776)
  b := (1194217/4398046511104)
  s := [(4398046507649/4398046511104),(-691/4398046511104),(-17/2199023255552)]
  L := [(2182827944738363270817395973/5316911983139663491615228241121378304),(775494840487/9444732965739290427392),(58162005649/14167099448608935641088),(1/590295810358705651712),(-1/885443715538058477568)]
  c := (969370337217/2361183241434822606848)
  R := (-135084607868641/12500000000000)
  total := (-10622731/40000000000000)
  k := 32
  n := 32
  sFloor := (1099511626731/2199023255552)
  nFloor := (479969756135/151115727451828646838272)
  eFloor := (114782493967/37778931862957161709568)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell044
