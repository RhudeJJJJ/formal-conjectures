/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (748047/34359738368)
  b := (1645703/68719476736)
  s := [(4397924857443/4398046511104),(-24329653/4398046511104),(-608121/2199023255552)]
  L := [(3131390747926540585003483589/162259276829213363391578010288128),(3337376992315/864691128455135232),(83424751549/432345564227567616),(-118165/54043195528445952),(-1465/27021597764222976)]
  c := (695308421489/36028797018963968)
  R := (-542773678739841/100000000000000)
  total := (-2927832611/250000000000000)
  k := 16
  n := 32
  sFloor := (1099474827887/2199023255552)
  nFloor := (1224723602409/36893488147419103232)
  eFloor := (1755422782591/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell091
