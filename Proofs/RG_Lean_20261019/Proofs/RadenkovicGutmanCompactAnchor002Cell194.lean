/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell194
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (418703/1048576)
  b := (460573/1048576)
  s := [(3929428981009/17592186044416),(-203871582205/17592186044416),(217737465/8796093022208)]
  L := [(1988938285911098337961/2361183241434822606848),(823990577887/26388279066624),(-1567957055/13194139533312),(-272946913/1649267441664),(14506787/824633720832)]
  c := (926171562593/1099511627776)
  R := (-2744990323/32000000000)
  total := (-3061485764161/1000000000000000)
  k := 1
  n := 32
  sFloor := (1862996436867/17592186044416)
  nFloor := (1870658761503/268435456)
  eFloor := (1409829004419/268435456)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell194
