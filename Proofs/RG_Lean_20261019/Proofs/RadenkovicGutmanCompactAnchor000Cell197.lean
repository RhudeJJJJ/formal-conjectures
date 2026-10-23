/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell197
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (557293/1048576)
  b := (306511/524288)
  s := [(6532510082595/35184372088832),(-60458253235/4398046511104),(3898581773/8796093022208)]
  L := [(2221473538065332442877/2361183241434822606848),(236082079367/6597069766656),(-4779668905/3298534883328),(-26768795/412316860416),(2570257/206158430208)]
  c := (2068908454911/2199023255552)
  R := (-1524803382507/50000000000000)
  total := (-1135336113769/1000000000000000)
  k := 1
  n := 32
  sFloor := (1516109595951/17592186044416)
  nFloor := (1216538936243/16777216)
  eFloor := (888087109857/16777216)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell197
