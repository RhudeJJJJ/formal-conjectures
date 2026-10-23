/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell175
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1095389/16777216)
  b := (1204927/16777216)
  s := [(2852200806317/17592186044416),(118551039327/17592186044416),(1547566373/8796093022208)]
  L := [(2220523756093153840201/2361183241434822606848),(-32639262935/1649267441664),(-101824825/412316860416),(103490257/824633720832),(-1967305/206158430208)]
  c := (2024216807971/2199023255552)
  R := (-2070760569451/50000000000000)
  total := (-117641207189/500000000000000)
  k := 1
  n := 32
  sFloor := (713050201579/8796093022208)
  nFloor := (832028152131/2199023255552)
  eFloor := (159468627143/549755813888)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell175
