/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell007
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (2043371/281474976710656)
  b := (561927/70368744177664)
  s := [(2199023255545/2199023255552),(-1/4398046511104),(-1/2199023255552)]
  L := [(2594158287909/1208925819614629174706176),(1556494211003/3626777458843887524118528),(12970778759/604462909807314587353088),(-11/226673591177742970257408),(1/37778931862957161709568)]
  c := (648539571977/302231454903657293676544)
  R := (-335843640300659/25000000000000)
  total := (-9717099/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255543/4398046511104)
  nFloor := (1142312056795/309485009821345068724781056)
  eFloor := (818650260083/309485009821345068724781056)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell007
