/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell094
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (995649/34359738368)
  b := (1095213/34359738368)
  s := [(2198890344345/2199023255552),(-53159173/4398046511104),(-1328403/2199023255552)]
  L := [(1456105597381/36028797018963968),(3494406642743/432345564227567616),(29112619367/72057594037927936),(-268943/27021597764222976),(-1119/4503599627370496)]
  c := (1456105597381/36028797018963968)
  R := (-505815417102503/100000000000000)
  total := (-3629181453/250000000000000)
  k := 15
  n := 32
  sFloor := (2198862436355/4398046511104)
  nFloor := (878992797647/18446744073709551616)
  eFloor := (1314580273463/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell094
