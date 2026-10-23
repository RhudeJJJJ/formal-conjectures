/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1257905/17592186044416)
  b := (1383695/17592186044416)
  s := [(2199023255407/2199023255552),(-59/4398046511104),(-1/2199023255552)]
  L := [(2602760069923/75557863725914323419136),(1561649834485/226673591177742970257408),(13013696873/37778931862957161709568),(11/14167099448608935641088),(-1/2361183241434822606848)]
  c := (1301380034961/37778931862957161709568)
  R := (-240915921593073/20000000000000)
  total := (-42892671/500000000000000)
  k := 35
  n := 32
  sFloor := (137438953461/274877906944)
  nFloor := (1288719147971/4835703278458516698824704)
  eFloor := (1232764322639/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell031
