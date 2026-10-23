/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell216
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (426041/131072)
  b := (468645/131072)
  s := [(742835429399/70368744177664),(-1447341091451/562949953421312),(95448207977/281474976710656)]
  L := [(2636215018300672084979/2361183241434822606848),(-95677015829/6597069766656),(3197911063/3298534883328),(-1707211/412316860416),(-1380391/206158430208)]
  c := (1212691165443/1099511627776)
  R := (2449397178847/50000000000000)
  total := (1055862075861/62500000000000)
  k := 0
  n := 32
  sFloor := (1171559689923/281474976710656)
  nFloor := 4975780991846335524412325888
  eFloor := 4363557146804490797664174080
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell216
