/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell095
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1095213/34359738368)
  b := (602367/17179869184)
  s := [(4397990058375/4398046511104),(-11290287/4398046511104),(-282229/2199023255552)]
  L := [(1090197834484983574931019357/162259276829213363391578010288128),(4647714650905/3458764513820540928),(116185995313/1729382256910270464),(-81919/216172782113783808),(-1021/108086391056891904)]
  c := (968290189793/144115188075855872)
  R := (-59552958148879/10000000000000)
  total := (-9414049359/500000000000000)
  k := 18
  n := 32
  sFloor := (2198989101815/4398046511104)
  nFloor := (900421161121/18446744073709551616)
  eFloor := (860097782549/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell095
