/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell076
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1432621/274877906944)
  b := (1575883/274877906944)
  s := [(4398037911067/4398046511104),(-26875/68719476736),(-5375/274877906944)]
  L := [(424305488830072517502140967/324518553658426726783156020576256),(3617836460843/13835058055282163712),(90445127519/6917529027641081856),(-8987/864691128455135232),(-119/432345564227567616)]
  c := (376858978539/288230376151711744)
  R := (-169342494753649/25000000000000)
  total := (-1752558133/500000000000000)
  k := 20
  n := 32
  sFloor := (2199018052533/4398046511104)
  nFloor := (909924582451/590295810358705651712)
  eFloor := (340210095779/295147905179352825856)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell076
