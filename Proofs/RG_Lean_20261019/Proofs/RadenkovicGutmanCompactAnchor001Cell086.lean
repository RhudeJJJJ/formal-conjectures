/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell086
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (928959/68719476736)
  b := (510927/34359738368)
  s := [(2199018178657/2199023255552),(-2030731/4398046511104),(-50767/2199023255552)]
  L := [(2786547547783/2305843009213693952),(139325674231/576460752303423488),(10449218353/864691128455135232),(-885/72057594037927936),(-1/3377699720527872)]
  c := (1393273773891/1152921504606846976)
  R := (-27252307013449/4000000000000)
  total := (-1143060437/125000000000000)
  k := 20
  n := 32
  sFloor := (549754278131/1099511627776)
  nFloor := (323900468231/36893488147419103232)
  eFloor := (154697650673/18446744073709551616)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell086
