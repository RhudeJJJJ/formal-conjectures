/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell091
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (748047/34359738368)
  b := (1645703/68719476736)
  s := [(4397914231423/4398046511104),(-26454667/4398046511104),(-661225/2199023255552)]
  L := [(2967589862747/144115188075855872),(890247224119/216172782113783808),(22253385815/108086391056891904),(-17099/6755399441055744),(-425/6755399441055744)]
  c := (1483794931373/72057594037927936)
  R := (-134882725582977/25000000000000)
  total := (-11640732311/1000000000000000)
  k := 16
  n := 32
  sFloor := (2198943227153/4398046511104)
  nFloor := (277219162099/9223372036854775808)
  eFloor := (1619679035385/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell091
