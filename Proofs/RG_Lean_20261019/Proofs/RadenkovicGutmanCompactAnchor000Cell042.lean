/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (448617/2199023255552)
  b := (986957/4398046511104)
  s := [(4398046497927/4398046511104),(-2637/4398046511104),(-65/2199023255552)]
  L := [(4730189371871/2361183241434822606848),(2838100961749/7083549724304467820544),(70952206837/3541774862152233910272),(-7/442721857769029238784),(-1/221360928884514619392)]
  c := (1182547342967/590295810358705651712)
  R := (-1955904635331/195312500000)
  total := (-40661861/200000000000000)
  k := 29
  n := 32
  sFloor := (549755811895/1099511627776)
  nFloor := (356906301829/151115727451828646838272)
  eFloor := (1067544536627/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell042
