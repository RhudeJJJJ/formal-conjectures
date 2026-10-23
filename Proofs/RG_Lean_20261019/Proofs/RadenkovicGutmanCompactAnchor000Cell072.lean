/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (244625/68719476736)
  b := (538175/137438953472)
  s := [(549755312389/549755813888),(-802399/4398046511104),(-20059/2199023255552)]
  L := [(395884174550145940847208471/649037107316853453566312041152512),(843877088975/6917529027641081856),(21096848773/3458764513820540928),(-977/432345564227567616),(-13/216172782113783808)]
  c := (43951972567/72057594037927936)
  R := (-715493938460799/100000000000000)
  total := (-505951373/200000000000000)
  k := 21
  n := 32
  sFloor := (2199020828297/4398046511104)
  nFloor := (53060879553/73786976294838206464)
  eFloor := (79355354323/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell072
