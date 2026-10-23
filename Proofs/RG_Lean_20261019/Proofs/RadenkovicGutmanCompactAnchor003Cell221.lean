/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell221
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (1372285/262144)
  b := (1509513/262144)
  s := [(3419735844357/1125899906842624),(-1856821819483/2251799813685248),(136237300455/1125899906842624)]
  L := [(19983535511263041901377/18889465931478580854784),(-125550515365/13194139533312),(2396879153/2199023255552),(-81797465/824633720832),(871963/137438953472)]
  c := (576914333969/549755813888)
  R := (1205489565071/50000000000000)
  total := (1705138752071/125000000000000)
  k := 0
  n := 32
  sFloor := (1313781117535/1125899906842624)
  nFloor := 9894439114731211014195626468433723392
  eFloor := 9296090184312739742955436269956497408
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell221
