/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell117
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1114405/4294967296)
  b := (1225845/4294967296)
  s := [(4379378000841/4398046511104),(-463731477/549755813888),(-44993141/1099511627776)]
  L := [(1802586076458802022312729/618970019642690137449562112),(1305860563205/2251799813685248),(96242020247/3377699720527872),(-6996545/140737488355328),(-246119/211106232532992)]
  c := (409860621507/140737488355328)
  R := (-1140397362307/390625000000)
  total := (-18624730327/250000000000000)
  k := 9
  n := 32
  sFloor := (1093872044115/2199023255552)
  nFloor := (307626666853/72057594037927936)
  eFloor := (1797339540129/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell117
