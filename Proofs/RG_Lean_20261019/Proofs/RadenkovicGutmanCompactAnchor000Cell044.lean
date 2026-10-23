/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (271413/1099511627776)
  b := (1194217/4398046511104)
  s := [(4398046491811/4398046511104),(-3857/4398046511104),(-97/2199023255552)]
  L := [(3462727852623/1180591620717411303424),(1038816437413/1770887431076116955136),(25970362649/885443715538058477568),(-5/55340232221128654848),(1/55340232221128654848)]
  c := (1731363926311/590295810358705651712)
  R := (-491180621202697/50000000000000)
  total := (-120649619/500000000000000)
  k := 29
  n := 32
  sFloor := (274877905485/549755813888)
  nFloor := (1045090838199/302231454903657293676544)
  eFloor := (390747168403/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell044
