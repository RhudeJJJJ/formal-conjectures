/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1257905/17592186044416)
  b := (1383695/17592186044416)
  s := [(4398046510819/4398046511104),(-57/4398046511104),(-1/2199023255552)]
  L := [(2554701465221/75557863725914323419136),(1532814786241/226673591177742970257408),(12773405799/37778931862957161709568),(-13/14167099448608935641088),(1/2361183241434822606848)]
  c := (638675366305/18889465931478580854784)
  R := (-37672233176807/3125000000000)
  total := (-85851973/1000000000000000)
  k := 35
  n := 32
  sFloor := (549755813845/1099511627776)
  nFloor := (1187802287795/4835703278458516698824704)
  eFloor := (567304594147/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell031
