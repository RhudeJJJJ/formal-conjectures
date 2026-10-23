/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell179
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (400939/4194304)
  b := (882065/8388608)
  s := [(400702234583/2199023255552),(340332149299/35184372088832),(-4344590249/17592186044416)]
  L := [(8209636636163082692401/9444732965739290427392),(-102701117919/4398046511104),(6565788439/6597069766656),(18026127/274877906944),(-3616639/412316860416)]
  c := (1862417939623/2199023255552)
  R := (-1661376759911/20000000000000)
  total := (-732682043157/1000000000000000)
  k := 1
  n := 32
  sFloor := (400702234583/4398046511104)
  nFloor := (1034503786003/1099511627776)
  eFloor := (411630516503/549755813888)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell179
