/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (510927/34359738368)
  b := (1124039/68719476736)
  s := [(4398034225049/4398046511104),(-2457189/4398046511104),(-61429/2199023255552)]
  L := [(3371714797979/2305843009213693952),(674338250757/2305843009213693952),(50574550075/3458764513820540928),(-1293/72057594037927936),(-97/216172782113783808)]
  c := (1685857398989/1152921504606846976)
  R := (-671776772057507/100000000000000)
  total := (-9917257367/1000000000000000)
  k := 20
  n := 32
  sFloor := (2199015822501/4398046511104)
  nFloor := (48989859703/4611686018427387904)
  eFloor := (187183828211/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell087
