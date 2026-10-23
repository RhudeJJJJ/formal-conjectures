/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (680043/34359738368)
  b := (748047/34359738368)
  s := [(4398024745737/4398046511104),(-2176511/2199023255552),(-27205/549755813888)]
  L := [(5973169594351/2305843009213693952),(1791933232397/3458764513820540928),(22398579559/864691128455135232),(-761/13510798882111488),(-19/13510798882111488)]
  c := (1493292398587/576460752303423488)
  R := (-321591979784641/50000000000000)
  total := (-126339447/10000000000000)
  k := 19
  n := 32
  sFloor := (2199010087537/4398046511104)
  nFloor := (1388613001843/73786976294838206464)
  eFloor := (1326427034003/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell090
