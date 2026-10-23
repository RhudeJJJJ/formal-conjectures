/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell088
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1124039/68719476736)
  b := (618221/34359738368)
  s := [(2198985920497/2199023255552),(-14933519/4398046511104),(-373291/2199023255552)]
  L := [(943027756067332856833709555/81129638414606681695789005144064),(2010133604893/864691128455135232),(50249451295/432345564227567616),(-43567/54043195528445952),(-547/27021597764222976)]
  c := (837576902117/72057594037927936)
  R := (-568123159575177/100000000000000)
  total := (-46067479/5000000000000)
  k := 17
  n := 32
  sFloor := (1099489040223/2199023255552)
  nFloor := (312966773183/18446744073709551616)
  eFloor := (1828537810639/147573952589676412928)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell088
