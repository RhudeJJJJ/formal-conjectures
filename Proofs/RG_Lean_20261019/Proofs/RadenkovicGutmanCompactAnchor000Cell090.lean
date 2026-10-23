/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell090
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (680043/34359738368)
  b := (748047/34359738368)
  s := [(4397922496425/4398046511104),(-1550111/274877906944),(-309959/1099511627776)]
  L := [(47802120837564761554654595/2535301200456458802993406410752),(815143777789/216172782113783808),(20376162665/108086391056891904),(-58523/27021597764222976),(-23/422212465065984)]
  c := (679308994301/36028797018963968)
  R := (-543937649859889/100000000000000)
  total := (-5334843529/500000000000000)
  k := 16
  n := 32
  sFloor := (1099474113703/2199023255552)
  nFloor := (1640232902673/73786976294838206464)
  eFloor := (1226527573749/73786976294838206464)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell090
