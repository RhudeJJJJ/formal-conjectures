/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell193
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1522557/4194304)
  b := (418703/1048576)
  s := [(1047129885829/4398046511104),(-432722118671/35184372088832),(4179611991/17592186044416)]
  L := [(7616851644063794558441/9444732965739290427392),(140765345271/4398046511104),(-3861366971/6597069766656),(-11795491/274877906944),(1546355/412316860416)]
  c := (1773436470903/2199023255552)
  R := (-10754705687569/100000000000000)
  total := (-888248384553/250000000000000)
  k := 1
  n := 32
  sFloor := (1988169047985/17592186044416)
  nFloor := (1027374871861/268435456)
  eFloor := (391980803391/134217728)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell193
