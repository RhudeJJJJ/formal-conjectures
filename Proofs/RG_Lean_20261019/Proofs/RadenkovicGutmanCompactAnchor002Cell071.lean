/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (444773/137438953472)
  b := (244625/68719476736)
  s := [(4398043588219/4398046511104),(-584571/4398046511104),(-14615/2199023255552)]
  L := [(2098292285161/4611686018427387904),(1258966024549/13835058055282163712),(7868463209/1729382256910270464),(-533/432345564227567616),(-7/216172782113783808)]
  c := (2098292285161/4611686018427387904)
  R := (-365074506560639/50000000000000)
  total := (-2347190657/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199021487209/4398046511104)
  nFloor := (24500914705/36893488147419103232)
  eFloor := (572595592885/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell071
