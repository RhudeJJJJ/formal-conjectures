/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell050
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1923295/4398046511104)
  b := (264453/549755813888)
  s := [(2199023228865/2199023255552),(-10675/4398046511104),(-267/2199023255552)]
  L := [(690241483332519436805368681/83076749736557242056487941267521536),(1471334372423/885443715538058477568),(36783261847/442721857769029238784),(-5/13835058055282163712),(-1/27670116110564327424)]
  c := (1226115179755/147573952589676412928)
  R := (-186059892008887/20000000000000)
  total := (-20235413/50000000000000)
  k := 27
  n := 32
  sFloor := (549755805815/1099511627776)
  nFloor := (1832556036637/151115727451828646838272)
  eFloor := (1338360121915/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell050
