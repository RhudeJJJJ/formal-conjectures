/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (244625/68719476736)
  b := (538175/137438953472)
  s := [(4398045792727/4398046511104),(-143673/4398046511104),(-3593/2199023255552)]
  L := [(443302134886286849287909435/5192296858534827628530496329220096),(3779820663941/221360928884514619392),(31498482953/36893488147419103232),(-827/13835058055282163712),(-5/2305843009213693952)]
  c := (1574925558451/18446744073709551616)
  R := (-406904760830573/50000000000000)
  total := (-1439868477/500000000000000)
  k := 24
  n := 32
  sFloor := (1099511410467/2199023255552)
  nFloor := (48737614955/73786976294838206464)
  eFloor := (186485916577/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell072
