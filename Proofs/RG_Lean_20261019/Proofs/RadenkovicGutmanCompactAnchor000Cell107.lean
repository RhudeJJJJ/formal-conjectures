/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell107
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (859307/8589934592)
  b := (945237/8589934592)
  s := [(2197440802661/2199023255552),(-158072885/1099511627776),(-1965909/274877906944)]
  L := [(76271976155108858299933525/158456325028528675187087900672),(866469160193/9007199254740992),(21598035567/4503599627370496),(-792535/562949953421312),(-9803/281474976710656)]
  c := (2167779943963/4503599627370496)
  R := (-23871652176953/6250000000000)
  total := (-4715552613/125000000000000)
  k := 12
  n := 32
  sFloor := (2197108929619/4398046511104)
  nFloor := (1309482711827/2305843009213693952)
  eFloor := (979200468631/2305843009213693952)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell107
