/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (607573/274877906944)
  b := (334165/137438953472)
  s := [(4398046239639/4398046511104),(-13573/1099511627776),(-679/1099511627776)]
  L := [(2383973174045/73786976294838206464),(238396124113/36893488147419103232),(35759232355/110680464442257309696),(-41/4611686018427387904),(-1/6917529027641081856)]
  c := (595993293511/18446744073709551616)
  R := (-862396215219319/100000000000000)
  total := (-947739071/500000000000000)
  k := 25
  n := 32
  sFloor := (2199023091315/4398046511104)
  nFloor := (554211327981/2361183241434822606848)
  eFloor := (529392198869/2361183241434822606848)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell067
