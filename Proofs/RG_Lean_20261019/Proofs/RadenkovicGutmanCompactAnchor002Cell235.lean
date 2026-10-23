/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell235
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1302807/65536)
  b := (1433087/65536)
  s := [(2269673601727/36028797018963968),(-1334637437731/72057594037927936),(105911531537/36028797018963968)]
  L := [(18981795330389867039479/18889465931478580854784),(-6305640601/6597069766656),(460282247/3298534883328),(-7274495/412316860416),(341125/206158430208)]
  c := (1103970814115/1099511627776)
  R := (202370227307/100000000000000)
  total := (883128930417/200000000000000)
  k := 0
  n := 32
  sFloor := (854133207199/36028797018963968)
  nFloor := 475036688574507437864372464591052359625145946522464637918642176
  eFloor := 472666505031197529602094908252065368356290987440137939703562240
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell235
