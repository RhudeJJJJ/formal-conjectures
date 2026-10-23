/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (874225/2199023255552)
  b := (1923295/4398046511104)
  s := [(4398046466993/4398046511104),(-8821/4398046511104),(-221/2199023255552)]
  L := [(4053273330227/590295810358705651712),(2431963973171/1770887431076116955136),(60799096951/885443715538058477568),(-53/110680464442257309696),(5/55340232221128654848)]
  c := (2026636665113/295147905179352825856)
  R := (-939830477917277/100000000000000)
  total := (-185853311/500000000000000)
  k := 28
  n := 32
  sFloor := (2199023228865/4398046511104)
  nFloor := (47328410037/4722366482869645213696)
  eFloor := (1106082745381/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell049
