/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (995485/70368744177664)
  b := (1095033/70368744177664)
  s := [(549755813881/549755813888),(-3/1099511627776)]
  L := [(1479342331702188829047658291/170141183460469231731687303715884105728),(262782666991/151115727451828646838272),(39417202073/453347182355485940514816),(-1/18889465931478580854784),(1/28334198897217871282176)]
  c := (656959967183/75557863725914323419136)
  R := (-159176855010823/12500000000000)
  total := (-448651/25000000000000)
  k := 37
  n := 32
  sFloor := (1099511627759/2199023255552)
  nFloor := (981894652835/77371252455336267181195264)
  eFloor := (1434202961329/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell014
