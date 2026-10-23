/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell078
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (866735/137438953472)
  b := (1906817/274877906944)
  s := [(4398035411531/4398046511104),(-17343/34359738368),(-27749/1099511627776)]
  L := [(3984107068513/2305843009213693952),(2390458078007/6917529027641081856),(59760835667/3458764513820540928),(-7709/432345564227567616),(-95/216172782113783808)]
  c := (124503345891/72057594037927936)
  R := (-663432184212019/100000000000000)
  total := (-2076646949/500000000000000)
  k := 20
  n := 32
  sFloor := (2199016540315/4398046511104)
  nFloor := (1488668914765/590295810358705651712)
  eFloor := (67950688533/36893488147419103232)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell078
