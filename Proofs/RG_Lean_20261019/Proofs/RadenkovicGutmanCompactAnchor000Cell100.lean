/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell100
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (220481/4294967296)
  b := (242529/4294967296)
  s := [(4397212414885/4398046511104),(-166770939/4398046511104),(-4163699/2199023255552)]
  L := [(1286131185355089949321513465/10141204801825835211973625643008),(2741011335547/108086391056891904),(68472011225/54043195528445952),(-661699/6755399441055744),(-8249/3377699720527872)]
  c := (1142313963735/9007199254740992)
  R := (-14019880399747/3125000000000)
  total := (-11391037499/500000000000000)
  k := 13
  n := 32
  sFloor := (1099259329137/2199023255552)
  nFloor := (1379320421491/9223372036854775808)
  eFloor := (1031423384991/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell100
