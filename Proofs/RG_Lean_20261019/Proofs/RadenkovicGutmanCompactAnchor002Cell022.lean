/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell022
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1066951/35184372088832)
  b := (586823/17592186044416)
  s := [(4398046510847/4398046511104),(-25/2199023255552),(-1/1099511627776)]
  L := [(3018689234913/75557863725914323419136),(603737281085/75557863725914323419136),(15093417897/37778931862957161709568),(-1/1180591620717411303424),(1/2361183241434822606848)]
  c := (94334038591/2361183241434822606848)
  R := (-1197167094881643/100000000000000)
  total := (-9039189/250000000000000)
  k := 35
  n := 32
  sFloor := (549755813849/1099511627776)
  nFloor := (1127935858549/19342813113834066795298816)
  eFloor := (1647517830807/38685626227668133590597632)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell022
