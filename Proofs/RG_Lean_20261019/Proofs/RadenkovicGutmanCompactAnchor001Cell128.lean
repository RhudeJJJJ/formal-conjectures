/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1589755/2147483648)
  b := (874365/1073741824)
  s := [(2183964460439/2199023255552),(-5958334697/4398046511104),(-141462051/2199023255552)]
  L := [(1113164869869433640077521/309485009821345068724781056),(4823023994825/6755399441055744),(38983968735/1125899906842624),(-44484881/422212465065984),(-166015/70368744177664)]
  c := (506208775673/140737488355328)
  R := (-140692561625883/50000000000000)
  total := (-204750503279/1000000000000000)
  k := 9
  n := 32
  sFloor := (2180843831039/4398046511104)
  nFloor := (948640192773/36028797018963968)
  eFloor := (453076589641/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell128
