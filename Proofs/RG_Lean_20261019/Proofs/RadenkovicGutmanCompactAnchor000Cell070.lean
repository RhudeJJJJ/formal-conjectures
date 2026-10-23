/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (808679/274877906944)
  b := (444773/137438953472)
  s := [(4398043770849/4398046511104),(-274021/2199023255552),(-6851/1099511627776)]
  L := [(270395176393070152680376719/649037107316853453566312041152512),(4611001636061/55340232221128654848),(115273465421/27670116110564327424),(-3683/3458764513820540928),(-41/1729382256910270464)]
  c := (960636641853/2305843009213693952)
  R := (-734555797197531/100000000000000)
  total := (-2146766977/1000000000000000)
  k := 22
  n := 32
  sFloor := (2199021597701/4398046511104)
  nFloor := (1159725198643/2361183241434822606848)
  eFloor := (216803803543/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell070
