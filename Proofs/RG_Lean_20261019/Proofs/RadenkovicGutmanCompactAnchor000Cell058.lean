/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell058
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1030685/1099511627776)
  b := (1133753/1099511627776)
  s := [(4398046232895/4398046511104),(-13911/1099511627776),(-695/1099511627776)]
  L := [(3120965528829/73786976294838206464),(1872570112435/221360928884514619392),(2925875857/6917529027641081856),(-83/6917529027641081856),(1/3458764513820540928)]
  c := (780241382207/18446744073709551616)
  R := (-848927519135637/100000000000000)
  total := (-197811347/250000000000000)
  k := 25
  n := 32
  sFloor := (2199023087235/4398046511104)
  nFloor := (941943119749/18889465931478580854784)
  eFloor := (1408725800243/37778931862957161709568)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell058
