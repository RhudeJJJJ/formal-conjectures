/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell120
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1483271/4294967296)
  b := (815799/2147483648)
  s := [(1090192795539/1099511627776),(-7360315167/4398046511104),(-173142251/2199023255552)]
  L := [(880670083779232035737985/154742504910672534362390528),(1270475421941/1125899906842624),(92000939041/1688849860263936),(-13398455/70368744177664),(-440629/105553116266496)]
  c := (800964775207/140737488355328)
  R := (-258441733964543/100000000000000)
  total := (-17519341971/200000000000000)
  k := 8
  n := 32
  sFloor := (2176532291243/4398046511104)
  nFloor := (487705270505/72057594037927936)
  eFloor := (91173753479/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell120
