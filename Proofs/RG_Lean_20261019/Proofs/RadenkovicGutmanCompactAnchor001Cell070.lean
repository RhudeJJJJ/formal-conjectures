/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell070
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (808679/274877906944)
  b := (444773/137438953472)
  s := [(1099511507547/1099511627776),(-96181/4398046511104),(-2405/2199023255552)]
  L := [(4223346754189/73786976294838206464),(844659848839/73786976294838206464),(63348753241/110680464442257309696),(-131/4611686018427387904),(-1/6917529027641081856)]
  c := (1055836688547/18446744073709551616)
  R := (-833803245879037/100000000000000)
  total := (-609686363/250000000000000)
  k := 25
  n := 32
  sFloor := (1099511482299/2199023255552)
  nFloor := (981817564863/2361183241434822606848)
  eFloor := (234462258931/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell070
