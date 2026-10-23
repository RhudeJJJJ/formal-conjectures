/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell240
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1049089/32768)
  b := (1153997/32768)
  s := [(2187099003241/144115188075855872),(-1291288857929/288230376151711744),(102879551471/144115188075855872)]
  L := [(37851235626648593232293/37778931862957161709568),(-2496004645/6597069766656),(7691239/137438953472),(-740075/103079215104),(23443/34359738368)]
  c := (275313582359/274877906944)
  R := (39593079367/50000000000000)
  total := (557120526519/200000000000000)
  k := 0
  n := 32
  sFloor := (1644334125747/288230376151711744)
  nFloor := 3690975547459246301000836869334333655608447042092638252621684132544512
  eFloor := 3683813199194676316210120136091324590636516080737917867417962593386496
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell240
