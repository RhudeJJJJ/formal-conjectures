/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell194
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (418703/1048576)
  b := (460573/1048576)
  s := [(3944984136219/17592186044416),(-105481575435/8796093022208),(108059297/1099511627776)]
  L := [(1985866235132314789339/2361183241434822606848),(105096897923/3298534883328),(-868259309/3298534883328),(-60257299/412316860416),(3331835/206158430208)]
  c := (1849482054945/2199023255552)
  R := (-8655382871899/100000000000000)
  total := (-3085430530257/1000000000000000)
  k := 1
  n := 32
  sFloor := (933937483525/8796093022208)
  nFloor := (517221663843/33554432)
  eFloor := (1558731717579/134217728)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell194
