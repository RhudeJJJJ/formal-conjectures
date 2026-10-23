/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell037
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (557113/4398046511104)
  b := (76603/549755813888)
  s := [(4398046506625/4398046511104),(-7/34359738368),(-11/1099511627776)]
  L := [(57915637591347614132086701/83076749736557242056487941267521536),(15431742727/110680464442257309696),(8230218413/1180591620717411303424),(11/442721857769029238784),(-1/73786976294838206464)]
  c := (1646061423097/2361183241434822606848)
  R := (-210840432856851/20000000000000)
  total := (-33231221/250000000000000)
  k := 31
  n := 32
  sFloor := (1099511626421/2199023255552)
  nFloor := (615052283235/604462909807314587353088)
  eFloor := (1796750401769/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell037
