/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell243
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1396335/32768)
  b := (47999/1024)
  s := [(3716605793839/576460752303423488),(-274597492757/144115188075855872),(87606989681/288230376151711744)]
  L := [(4727496345433553459187/4722366482869645213696),(-947880483/4398046511104),(211177685/6597069766656),(-1134031/274877906944),(162295/412316860416)]
  c := (1100500139801/1099511627776)
  R := (44932127459/100000000000000)
  total := (2104545766077/1000000000000000)
  k := 0
  n := 32
  sFloor := (698357450543/288230376151711744)
  nFloor := 3391523009389379598959331957182335720383046735738984828503223929097933092290560
  eFloor := 3387799142316787763065638601857791957512955399513549992896242538811837441376256
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell243
