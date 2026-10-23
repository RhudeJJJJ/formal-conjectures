/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell131
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1057981/1073741824)
  b := (1163779/1073741824)
  s := [(4150101306693/4398046511104),(-22722734973/2199023255552),(-22198363/68719476736)]
  L := [(48013272818937237437031/1208925819614629174706176),(1580205253855/211106232532992),(10174645609/35184372088832),(-96711505/13194139533312),(-86005/2199023255552)]
  c := (1397370151795/35184372088832)
  R := (-80650250054389/50000000000000)
  total := (-38613672423/250000000000000)
  k := 5
  n := 32
  sFloor := (2051617570757/4398046511104)
  nFloor := (138642379733/2251799813685248)
  eFloor := (1620085811417/36028797018963968)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell131
