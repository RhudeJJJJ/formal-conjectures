/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell119
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1348429/4294967296)
  b := (1483271/4294967296)
  s := [(4370795518647/4398046511104),(-2699702159/2199023255552),(-64566593/1099511627776)]
  L := [(1316931940081972714639119/309485009821345068724781056),(952122112419/1125899906842624),(23201096677/562949953421312),(-7406621/70368744177664),(-84225/35184372088832)]
  c := (299435655525/70368744177664)
  R := (-272980245699317/100000000000000)
  total := (-84193636447/1000000000000000)
  k := 8
  n := 32
  sFloor := (1091284461989/2199023255552)
  nFloor := (1801586652019/288230376151711744)
  eFloor := (20558505771/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell119
