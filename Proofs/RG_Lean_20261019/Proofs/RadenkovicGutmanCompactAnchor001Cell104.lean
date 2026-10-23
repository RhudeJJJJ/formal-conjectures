/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell104
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (645611/8589934592)
  b := (177543/2147483648)
  s := [(4397732670637/4398046511104),(-62760909/4398046511104),(-1568191/2199023255552)]
  L := [(6060968693451840719384871463/162259276829213363391578010288128),(538279131463/72057594037927936),(40358215301/108086391056891904),(-52731/4503599627370496),(-1973/6755399441055744)]
  c := (168225674875/4503599627370496)
  R := (-50975405856821/10000000000000)
  total := (-18974383587/500000000000000)
  k := 15
  n := 32
  sFloor := (2198833386673/4398046511104)
  nFloor := (625778362413/2305843009213693952)
  eFloor := (149438558235/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell104
