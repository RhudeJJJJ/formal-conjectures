/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell039
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (337053/2199023255552)
  b := (1483033/8796093022208)
  s := [(4398046504547/4398046511104),(-1311/4398046511104),(-33/2199023255552)]
  L := [(4819986617505/4722366482869645213696),(2891987675953/14167099448608935641088),(24099861427/2361183241434822606848),(-19/885443715538058477568),(1/147573952589676412928)]
  c := (150624581797/147573952589676412928)
  R := (-129392529579877/12500000000000)
  total := (-39479467/250000000000000)
  k := 30
  n := 32
  sFloor := (2199023251585/4398046511104)
  nFloor := (1800992195123/1208925819614629174706176)
  eFloor := (657654141439/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell039
