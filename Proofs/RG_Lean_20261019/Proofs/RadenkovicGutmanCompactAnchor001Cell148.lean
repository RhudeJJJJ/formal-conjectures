/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell148
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (334219/67108864)
  b := (1470563/268435456)
  s := [(6937201736453/8796093022208),(-254457453681/8796093022208),(1765739927/4398046511104)]
  L := [(2336921646623250344363/18889465931478580854784),(998750803595/52776558133248),(2547520777/26388279066624),(-33404633/824633720832),(3170405/1649267441664)]
  c := (2176427884607/17592186044416)
  R := (-4179539761799/4000000000000)
  total := (-502194583431/1000000000000000)
  k := 4
  n := 32
  sFloor := (104473058791/274877906944)
  nFloor := (672396158927/562949953421312)
  eFloor := (642147895479/562949953421312)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell148
