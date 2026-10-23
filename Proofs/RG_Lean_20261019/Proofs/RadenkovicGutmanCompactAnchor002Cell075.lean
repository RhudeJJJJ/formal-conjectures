/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1302383/274877906944)
  b := (1432621/274877906944)
  s := [(4398040245661/4398046511104),(-313271/1099511627776),(-15663/1099511627776)]
  L := [(1266035995986477194623240007/1298074214633706907132624082305024),(2698707896503/13835058055282163712),(67467149327/6917529027641081856),(-4921/864691128455135232),(-59/432345564227567616)]
  c := (562232925099/576460752303423488)
  R := (-346012539864723/50000000000000)
  total := (-1627950613/500000000000000)
  k := 20
  n := 32
  sFloor := (1099509732481/2199023255552)
  nFloor := (1680633021241/1180591620717411303424)
  eFloor := (76712941207/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell075
