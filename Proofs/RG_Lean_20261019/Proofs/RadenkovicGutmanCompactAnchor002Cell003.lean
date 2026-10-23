/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell003
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1395653/281474976710656)
  b := (767609/140737488355328)
  s := [(4398046511097/4398046511104),(-1/2199023255552)]
  L := [(5165166948219/4835703278458516698824704),(193693344205/906694364710971881029632),(12912861873/1208925819614629174706176),(-11/453347182355485940514816),(1/75557863725914323419136)]
  c := (645645868527/604462909807314587353088)
  R := (-344563878311913/25000000000000)
  total := (-1361973/200000000000000)
  k := 40
  n := 32
  sFloor := (2199023255547/4398046511104)
  nFloor := (964984561605/618970019642690137449562112)
  eFloor := (88093953861/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell003
