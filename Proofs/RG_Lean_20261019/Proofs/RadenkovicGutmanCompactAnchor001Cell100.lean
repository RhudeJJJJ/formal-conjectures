/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell100
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (220481/4294967296)
  b := (242529/4294967296)
  s := [(549737511579/549755813888),(-915063/137438953472),(-182967/549755813888)]
  L := [(706904422886646460478473015/40564819207303340847894502572032),(1506795471119/432345564227567616),(37664205929/216172782113783808),(-34429/13510798882111488),(-863/13510798882111488)]
  c := (313928626599/18014398509481984)
  R := (-547875812852233/100000000000000)
  total := (-27876450809/1000000000000000)
  k := 16
  n := 32
  sFloor := (68716708545/137438953472)
  nFloor := (145965732441/1152921504606846976)
  eFloor := (278857953317/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell100
