/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (995485/70368744177664)
  b := (1095033/70368744177664)
  s := [(1099511627763/1099511627776),(-9/4398046511104),(-1/2199023255552)]
  L := [(1386440514190546930427812039/170141183460469231731687303715884105728),(492560143973/302231454903657293676544),(36941825255/453347182355485940514816),(-1/18889465931478580854784),(1/28334198897217871282176)]
  c := (1231406544901/151115727451828646838272)
  R := (-638328868467457/50000000000000)
  total := (-4497979/250000000000000)
  k := 37
  n := 32
  sFloor := (68719476735/137438953472)
  nFloor := (542237746103/38685626227668133590597632)
  eFloor := (1554402124125/154742504910672534362390528)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell014
