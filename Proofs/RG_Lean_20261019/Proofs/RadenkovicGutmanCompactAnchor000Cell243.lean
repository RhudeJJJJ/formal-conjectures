/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell243
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1396335/32768)
  b := (47999/1024)
  s := [(3716605793839/576460752303423488),(-274597492757/144115188075855872),(87606989681/288230376151711744)]
  L := [(9454992690857226368785/9444732965739290427392),(-947880483/4398046511104),(211177685/6597069766656),(-1134031/274877906944),(162295/412316860416)]
  c := (137562517475/137438953472)
  R := (44932127413/100000000000000)
  total := (1052272881913/500000000000000)
  k := 0
  n := 32
  sFloor := (698357450543/288230376151711744)
  nFloor := 1026312029977071821744630200283441160920202793737982550433279001220874240
  eFloor := 1025185146991592434810106902440207037569201402035531724868562948062183424
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell243
