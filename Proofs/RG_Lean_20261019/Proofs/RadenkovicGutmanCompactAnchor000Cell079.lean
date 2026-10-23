/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell079
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1906817/274877906944)
  b := (1048749/137438953472)
  s := [(2199015637837/2199023255552),(-761765/1099511627776),(-38087/1099511627776)]
  L := [(1503361355604996852580404083/649037107316853453566312041152512),(534097399441/1152921504606846976),(40056592339/1729382256910270464),(-2353/72057594037927936),(-91/108086391056891904)]
  c := (1335253113059/576460752303423488)
  R := (-4054856770447/625000000000)
  total := (-1116736299/250000000000000)
  k := 19
  n := 32
  sFloor := (2199014038133/4398046511104)
  nFloor := (50374508851/18446744073709551616)
  eFloor := (1205403916101/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell079
