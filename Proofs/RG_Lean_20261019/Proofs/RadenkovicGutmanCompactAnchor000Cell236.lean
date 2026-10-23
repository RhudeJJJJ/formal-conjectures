/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell236
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1433087/65536)
  b := (1576395/65536)
  s := [(3416532828797/72057594037927936),(-251414363263/18014398509481984),(79894382929/36028797018963968)]
  L := [(4741518542866429189403/4722366482869645213696),(-5247044945/6597069766656),(384353873/3298534883328),(-6098677/412316860416),(287023/206158430208)]
  c := (1103209692349/1099511627776)
  R := (167886332857/100000000000000)
  total := (4030673687583/1000000000000000)
  k := 0
  n := 32
  sFloor := (1285332070801/72057594037927936)
  nFloor := 195745497489221911299435118317036356750378401595139637116928
  eFloor := 194936351004767350868994771678691139747502057696069542739968
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell236
