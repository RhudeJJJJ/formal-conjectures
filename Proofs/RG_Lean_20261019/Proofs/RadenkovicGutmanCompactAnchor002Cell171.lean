/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell171
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (748167/16777216)
  b := (1645967/33554432)
  s := [(1280209118339/8796093022208),(67145261831/35184372088832),(8552860377/17592186044416)]
  L := [(9398000216523944786865/9444732965739290427392),(-55068348221/6597069766656),(-2039154553/1649267441664),(30391597/206158430208),(-527281/51539607552)]
  c := (2167369130373/2199023255552)
  R := (-181240466543/25000000000000)
  total := (-4257957953/200000000000000)
  k := 1
  n := 32
  sFloor := (1280209118339/17592186044416)
  nFloor := (1302481770745/8796093022208)
  eFloor := (976348282655/8796093022208)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell171
