/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (21435/17179869184)
  b := (47157/34359738368)
  s := [(2199023212303/2199023255552),(-4325/1099511627776),(-27/137438953472)]
  L := [(6076890072525/590295810358705651712),(3646133964769/1770887431076116955136),(91153341217/885443715538058477568),(-97/110680464442257309696),(-1/55340232221128654848)]
  c := (1519222518131/147573952589676412928)
  R := (-91958206394103/10000000000000)
  total := (-285326427/250000000000000)
  k := 27
  n := 32
  sFloor := (2199023203221/4398046511104)
  nFloor := (706358862823/9444732965739290427392)
  eFloor := (168681535685/2361183241434822606848)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell061
