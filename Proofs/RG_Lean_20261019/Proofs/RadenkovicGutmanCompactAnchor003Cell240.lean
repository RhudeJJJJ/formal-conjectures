/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell240
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1049089/32768)
  b := (1153997/32768)
  s := [(2187099003241/144115188075855872),(-1291288857927/288230376151711744),(51439775735/72057594037927936)]
  L := [(75702471253389711012481/75557863725914323419136),(-2496004645/6597069766656),(7691239/137438953472),(-740075/103079215104),(23443/34359738368)]
  c := (1101254329437/1099511627776)
  R := (79186158779/100000000000000)
  total := (2785602634539/1000000000000000)
  k := 0
  n := 32
  sFloor := (1644334125747/288230376151711744)
  nFloor := 3892999402870181295282323971810494903749297645411160342430483921984284524544
  eFloor := 3885445026757359386865563354696489989271853929782406808327122621111220568064
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell240
