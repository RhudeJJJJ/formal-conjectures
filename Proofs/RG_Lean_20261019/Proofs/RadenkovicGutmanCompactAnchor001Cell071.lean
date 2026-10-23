/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell071
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (444773/137438953472)
  b := (244625/68719476736)
  s := [(4398045929197/4398046511104),(-29095/1099511627776),(-1455/1099511627776)]
  L := [(2555119551541/36893488147419103232),(1022040778345/73786976294838206464),(76652496889/110680464442257309696),(-193/4611686018427387904),(-1/6917529027641081856)]
  c := (638779887885/9223372036854775808)
  R := (-206068082583719/25000000000000)
  total := (-2651785719/1000000000000000)
  k := 24
  n := 32
  sFloor := (1099511451749/2199023255552)
  nFloor := (296999212443/590295810358705651712)
  eFloor := (567397518571/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell071
