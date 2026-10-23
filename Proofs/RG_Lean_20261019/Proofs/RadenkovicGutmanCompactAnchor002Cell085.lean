/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell085
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (844509/68719476736)
  b := (928959/68719476736)
  s := [(4398004361113/4398046511104),(-8429785/4398046511104),(-210729/2199023255552)]
  L := [(1064641905356687968246858379/162259276829213363391578010288128),(2269374312067/1729382256910270464),(56731531309/864691128455135232),(-27763/108086391056891904),(-349/54043195528445952)]
  c := (472795982523/72057594037927936)
  R := (-298357807638913/50000000000000)
  total := (-7273607687/1000000000000000)
  k := 18
  n := 32
  sFloor := (2198997754935/4398046511104)
  nFloor := (1413298895757/147573952589676412928)
  eFloor := (1032166465243/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell085
