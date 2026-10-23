/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell072
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (244625/68719476736)
  b := (538175/137438953472)
  s := [(4398045806997/4398046511104),(-70411/2199023255552),(-55/34359738368)]
  L := [(6183381542921/73786976294838206464),(1236676091117/73786976294838206464),(92750641583/110680464442257309696),(-271/4611686018427387904),(-11/6917529027641081856)]
  c := (772922692865/9223372036854775808)
  R := (-814741375198713/100000000000000)
  total := (-2883054131/1000000000000000)
  k := 24
  n := 32
  sFloor := (2199022829567/4398046511104)
  nFloor := (718737212827/1180591620717411303424)
  eFloor := (686550155639/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell072
