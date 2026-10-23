/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell100
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (220481/4294967296)
  b := (242529/4294967296)
  s := [(1099327801713/1099511627776),(-147023167/4398046511104),(-3671237/2199023255552)]
  L := [(4124274752239/36028797018963968),(206177581967/9007199254740992),(7726342355/6755399441055744),(-87997/1125899906842624),(-1645/844424930131968)]
  c := (2062137376119/18014398509481984)
  R := (-453759181408941/100000000000000)
  total := (-1152252807/50000000000000)
  k := 14
  n := 32
  sFloor := (2198578420605/4398046511104)
  nFloor := (1541302443205/9223372036854775808)
  eFloor := (140706325337/1152921504606846976)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell100
