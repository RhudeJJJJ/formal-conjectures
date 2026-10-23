/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell087
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (510927/34359738368)
  b := (1124039/68719476736)
  s := [(4397984799949/4398046511104),(-12341921/4398046511104),(-308517/2199023255552)]
  L := [(692214892139/72057594037927936),(1661285424433/864691128455135232),(41529591709/432345564227567616),(-29761/54043195528445952),(-373/27021597764222976)]
  c := (692214892139/72057594037927936)
  R := (-577653991461331/100000000000000)
  total := (-851766429/100000000000000)
  k := 17
  n := 32
  sFloor := (2198985920497/4398046511104)
  nFloor := (1034601635465/73786976294838206464)
  eFloor := (1511189341955/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell087
