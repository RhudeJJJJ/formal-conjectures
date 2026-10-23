/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell110
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (142967/1073741824)
  b := (1258109/8589934592)
  s := [(4397061791181/4398046511104),(-24609147/549755813888),(-2456825/1099511627776)]
  L := [(1055745479027/9007199254740992),(2533152714841/108086391056891904),(63266190169/54043195528445952),(-778225/6755399441055744),(-9697/3377699720527872)]
  c := (1055745479027/9007199254740992)
  R := (-226288308029101/50000000000000)
  total := (-59615187997/1000000000000000)
  k := 14
  n := 32
  sFloor := (274803443169/549755813888)
  nFloor := (981975800857/1152921504606846976)
  eFloor := (938000042893/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell110
