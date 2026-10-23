/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell103
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1173839/17179869184)
  b := (645611/8589934592)
  s := [(4397787133319/4398046511104),(-25935159/2199023255552),(-648091/1099511627776)]
  L := [(78267814993392722942175261/2535301200456458802993406410752),(222434393923/36028797018963968),(16678128967/54043195528445952),(-36013/4503599627370496),(-169/844424930131968)]
  c := (1112252547747/36028797018963968)
  R := (-519284326677133/100000000000000)
  total := (-7029970703/200000000000000)
  k := 15
  n := 32
  sFloor := (1099433167659/2199023255552)
  nFloor := (64646609131/288230376151711744)
  eFloor := (988024818991/4611686018427387904)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell103
