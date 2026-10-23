/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell141
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (343015/134217728)
  b := (754633/268435456)
  s := [(6517103368157/8796093022208),(-291567899169/8796093022208),(3055551019/4398046511104)]
  L := [(3848912509355411213571/18889465931478580854784),(526422354803/17592186044416),(135118571/26388279066624),(-32815517/549755813888),(5801023/1649267441664)]
  c := (1792289553841/8796093022208)
  R := (-39770344131619/50000000000000)
  total := (-97165830131/500000000000000)
  k := 3
  n := 32
  sFloor := (389477910689/1099511627776)
  nFloor := (1866275539907/4503599627370496)
  eFloor := (1363119418041/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell141
