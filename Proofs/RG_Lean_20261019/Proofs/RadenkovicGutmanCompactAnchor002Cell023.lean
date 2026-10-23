/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (586823/17592186044416)
  b := (645505/17592186044416)
  s := [(4398046510793/4398046511104),(-63/4398046511104),(-1/2199023255552)]
  L := [(8224954064957398414488177167/170141183460469231731687303715884105728),(547889201753/56668397794435742564352),(1712145001/3541774862152233910272),(7/14167099448608935641088),(-1/3541774862152233910272)]
  c := (1826306675879/37778931862957161709568)
  R := (-1187636085422307/100000000000000)
  total := (-19727169/500000000000000)
  k := 35
  n := 32
  sFloor := (549755813841/1099511627776)
  nFloor := (682401078135/9671406556917033397649408)
  eFloor := (996748117783/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell023
