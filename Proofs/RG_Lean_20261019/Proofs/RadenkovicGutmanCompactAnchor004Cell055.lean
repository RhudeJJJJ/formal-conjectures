/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1548741/2199023255552)
  b := (851807/1099511627776)
  s := [(4398046383787/4398046511104),(-6365/1099511627776),(-319/1099511627776)]
  L := [(419468536898710070835806759/20769187434139310514121985316880384),(894144588083/221360928884514619392),(14902302177/73786976294838206464),(-29/13835058055282163712),(-1/4611686018427387904)]
  c := (745125804433/36893488147419103232)
  R := (-55367961969737/6250000000000)
  total := (-620504403/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023178525/4398046511104)
  nFloor := (656217640583/18889465931478580854784)
  eFloor := (940570904323/37778931862957161709568)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell055
