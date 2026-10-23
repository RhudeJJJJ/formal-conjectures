/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell073
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (538175/137438953472)
  b := (1183985/274877906944)
  s := [(1099510643873/1099511627776),(-787119/4398046511104),(-19679/2199023255552)]
  L := [(810416802278320207717549665/1298074214633706907132624082305024),(1727505732847/13835058055282163712),(43187485085/6917529027641081856),(-31/13510798882111488),(-23/432345564227567616)]
  c := (1439589429491/2305843009213693952)
  R := (-714329947185161/100000000000000)
  total := (-1389087333/500000000000000)
  k := 21
  n := 32
  sFloor := (2199020874507/4398046511104)
  nFloor := (1267819221885/1180591620717411303424)
  eFloor := (908596324325/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell073
