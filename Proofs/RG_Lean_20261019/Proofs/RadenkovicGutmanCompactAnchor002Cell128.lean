/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell128
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1589755/2147483648)
  b := (874365/1073741824)
  s := [(4252739827209/4398046511104),(-3453590413/549755813888),(-33462407/137438953472)]
  L := [(6951049527132741482011/302231454903657293676544),(1876520920129/422212465065984),(40628256163/211106232532992),(-36072707/13194139533312),(-478033/13194139533312)]
  c := (101151083467/4398046511104)
  R := (-188615023576351/100000000000000)
  total := (-136174073643/1000000000000000)
  k := 6
  n := 32
  sFloor := (66000629795/137438953472)
  nFloor := (626059349917/18014398509481984)
  eFloor := (1828920306737/72057594037927936)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell128
