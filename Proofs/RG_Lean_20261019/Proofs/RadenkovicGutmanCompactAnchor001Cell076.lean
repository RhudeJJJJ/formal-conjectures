/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1432621/274877906944)
  b := (1575883/274877906944)
  s := [(4398045001791/4398046511104),(-301861/4398046511104),(-7547/2199023255552)]
  L := [(3313652272369/18446744073709551616),(248523653269/6917529027641081856),(24852310529/13835058055282163712),(-59/216172782113783808),(-5/864691128455135232)]
  c := (207103267023/1152921504606846976)
  R := (-776617372663711/100000000000000)
  total := (-2011188939/500000000000000)
  k := 23
  n := 32
  sFloor := (1099511171209/2199023255552)
  nFloor := (192584402581/147573952589676412928)
  eFloor := (367919871657/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell076
