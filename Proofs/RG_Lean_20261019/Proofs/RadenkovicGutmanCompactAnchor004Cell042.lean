/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (448617/2199023255552)
  b := (986957/4398046511104)
  s := [(4398046500421/4398046511104),(-2137/4398046511104),(-53/2199023255552)]
  L := [(125041298077/73786976294838206464),(2400782214001/7083549724304467820544),(60019287215/3541774862152233910272),(-13/442721857769029238784),(1/221360928884514619392)]
  c := (125041298077/73786976294838206464)
  R := (-1009790200632833/100000000000000)
  total := (-205016233/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023249089/4398046511104)
  nFloor := (440485635473/151115727451828646838272)
  eFloor := (631357566259/302231454903657293676544)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell042
