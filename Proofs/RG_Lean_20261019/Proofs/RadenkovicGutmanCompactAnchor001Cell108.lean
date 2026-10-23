/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell108
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (945237/8589934592)
  b := (64985/536870912)
  s := [(4397373856905/4398046511104),(-134497283/4398046511104),(-3358603/2199023255552)]
  L := [(3171631706538284185121347/39614081257132168796771975168),(1153630511487/72057594037927936),(86463508615/108086391056891904),(-242137/4503599627370496),(-9067/6755399441055744)]
  c := (1442291116535/18014398509481984)
  R := (-47163468659777/10000000000000)
  total := (-5136576989/100000000000000)
  k := 14
  n := 32
  sFloor := (274827040151/549755813888)
  nFloor := (670703229253/1152921504606846976)
  eFloor := (160166800339/288230376151711744)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell108
