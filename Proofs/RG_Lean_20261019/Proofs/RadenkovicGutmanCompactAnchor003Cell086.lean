/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (928959/68719476736)
  b := (510927/34359738368)
  s := [(4398036151533/4398046511104),(-1035943/2199023255552),(-12949/549755813888)]
  L := [(24971821990719103754228771/20282409603651670423947251286016),(1703359586117/6917529027641081856),(21291568751/1729382256910270464),(-5489/432345564227567616),(-35/108086391056891904)]
  c := (1419483737135/1152921504606846976)
  R := (-680375823877941/100000000000000)
  total := (-9131886729/1000000000000000)
  k := 20
  n := 32
  sFloor := (2199016988027/4398046511104)
  nFloor := (87854843563/9223372036854775808)
  eFloor := (168080557661/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell086
