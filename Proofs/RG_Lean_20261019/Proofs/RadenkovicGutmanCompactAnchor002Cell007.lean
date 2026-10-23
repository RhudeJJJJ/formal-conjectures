/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (2043371/281474976710656)
  b := (561927/70368744177664)
  s := [(4398046511089/4398046511104),(-5/4398046511104),(1/2199023255552)]
  L := [(691996542795/302231454903657293676544),(3321581779879/7253554917687775048237056),(83039503825/3626777458843887524118528),(5/453347182355485940514816),(-1/226673591177742970257408)]
  c := (691996542795/302231454903657293676544)
  R := (-83758229022141/6250000000000)
  total := (-9693557/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255543/4398046511104)
  nFloor := (258565110161/77371252455336267181195264)
  eFloor := (1510690971249/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell007
