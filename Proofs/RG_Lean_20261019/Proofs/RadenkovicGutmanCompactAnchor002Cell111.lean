/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell111
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1258109/8589934592)
  b := (1383919/8589934592)
  s := [(274504490459/274877906944),(-1192481155/4398046511104),(-29527083/2199023255552)]
  L := [(1152132672105081163548319/1237940039285380274899124224),(837117477015/4503599627370496),(62434952405/6755399441055744),(-1446789/281474976710656),(-53177/422212465065984)]
  c := (1047858561019/1125899906842624)
  R := (-174489732403441/50000000000000)
  total := (-25202178547/500000000000000)
  k := 11
  n := 32
  sFloor := (2195410156011/4398046511104)
  nFloor := (98019566755/72057594037927936)
  eFloor := (572688720187/576460752303423488)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell111
