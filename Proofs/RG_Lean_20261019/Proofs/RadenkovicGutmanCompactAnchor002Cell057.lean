/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell057
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (936987/1099511627776)
  b := (1030685/1099511627776)
  s := [(2199023154209/2199023255552),(-40537/4398046511104),(-1013/2199023255552)]
  L := [(1164036426857/36893488147419103232),(2793666421943/442721857769029238784),(23280375243/73786976294838206464),(-185/27670116110564327424),(1/4611686018427387904)]
  c := (1164036426857/36893488147419103232)
  R := (-431791299427441/50000000000000)
  total := (-146360269/200000000000000)
  k := 25
  n := 32
  sFloor := (2199023132927/4398046511104)
  nFloor := (869886487909/18889465931478580854784)
  eFloor := (1270598402171/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell057
