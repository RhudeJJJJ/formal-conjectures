/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell038
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (76603/549755813888)
  b := (337053/2199023255552)
  s := [(4398046505685/4398046511104),(-543/2199023255552),(-13/1099511627776)]
  L := [(497933092865/590295810358705651712),(2390063242337/14167099448608935641088),(59751190717/7083549724304467820544),(1/885443715538058477568),(-1/442721857769029238784)]
  c := (497933092865/590295810358705651712)
  R := (-522335597634197/50000000000000)
  total := (-72444549/500000000000000)
  k := 31
  n := 32
  sFloor := (2199023252273/4398046511104)
  nFloor := (1488425068151/1208925819614629174706176)
  eFloor := (67939558049/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell038
