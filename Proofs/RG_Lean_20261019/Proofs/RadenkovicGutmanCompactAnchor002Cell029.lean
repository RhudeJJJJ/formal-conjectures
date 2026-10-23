/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell029
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1039591/17592186044416)
  b := (571775/8796093022208)
  s := [(4398046510129/4398046511104),(-195/4398046511104),(-5/2199023255552)]
  L := [(201666740518148842731947005/1329227995784915872903807060280344576),(429878098961/14167099448608935641088),(5373471053/3541774862152233910272),(1/221360928884514619392),(-1/442721857769029238784)]
  c := (1432928375195/9444732965739290427392)
  R := (-113045014498843/10000000000000)
  total := (-66516601/1000000000000000)
  k := 33
  n := 32
  sFloor := (1099511627481/2199023255552)
  nFloor := (267707466985/1208925819614629174706176)
  eFloor := (782053025365/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell029
