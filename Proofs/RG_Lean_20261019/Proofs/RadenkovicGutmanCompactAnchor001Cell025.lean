/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell025
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1420111/35184372088832)
  b := (781061/17592186044416)
  s := [(4398046511013/4398046511104),(-17/4398046511104),(-1/2199023255552)]
  L := [(458246175858264380434695157/42535295865117307932921825928971026432),(1302413048627/604462909807314587353088),(97680909821/906694364710971881029632),(5/37778931862957161709568),(-5/56668397794435742564352)]
  c := (1628017457229/151115727451828646838272)
  R := (-631348719913769/50000000000000)
  total := (-50769559/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255497/4398046511104)
  nFloor := (378471396071/4835703278458516698824704)
  eFloor := (361522391311/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell025
