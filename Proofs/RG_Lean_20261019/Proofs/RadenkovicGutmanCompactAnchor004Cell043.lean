/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (986957/4398046511104)
  b := (271413/1099511627776)
  s := [(2199023249089/2199023255552),(-2585/4398046511104),(-65/2199023255552)]
  L := [(4841595134549/2361183241434822606848),(484156078099/1180591620717411303424),(18155723917/885443715538058477568),(1/73786976294838206464),(-1/55340232221128654848)]
  c := (1210398783637/590295810358705651712)
  R := (-1000259223207133/100000000000000)
  total := (-223378361/1000000000000000)
  k := 29
  n := 32
  sFloor := (2199023247731/4398046511104)
  nFloor := (2131948747593/604462909807314587353088)
  eFloor := (1527884071887/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell043
