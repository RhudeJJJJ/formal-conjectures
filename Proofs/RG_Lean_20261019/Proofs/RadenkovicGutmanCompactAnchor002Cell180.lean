/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell180
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (882065/8388608)
  b := (1940543/16777216)
  s := [(900366802137/4398046511104),(365222086475/35184372088832),(-8459194833/17592186044416)]
  L := [(244486862729755332241/295147905179352825856),(-646959875939/26388279066624),(7433393845/4398046511104),(43056929/1649267441664),(-2503481/274877906944)]
  c := (1771409830975/2199023255552)
  R := (-1081187714089/10000000000000)
  total := (-532483590921/500000000000000)
  k := 1
  n := 32
  sFloor := (900366802137/8796093022208)
  nFloor := (874110045265/549755813888)
  eFloor := (174150409419/137438953472)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell180
