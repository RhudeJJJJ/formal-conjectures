/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell235
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1302807/65536)
  b := (1433087/65536)
  s := [(2269673601727/36028797018963968),(-1334637437731/72057594037927936),(105911531537/36028797018963968)]
  L := [(4745448832606002566875/4722366482869645213696),(-6305640601/6597069766656),(460282247/3298534883328),(-7274495/412316860416),(341125/206158430208)]
  c := (1103970814117/1099511627776)
  R := (101185113699/50000000000000)
  total := (2207822326941/500000000000000)
  k := 0
  n := 32
  sFloor := (854133207199/36028797018963968)
  nFloor := 188676883591668199182966377727108382257965669886135031622537314304
  eFloor := 187735485052891021466697562869263869626442922987760925531594293248
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell235
