/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1183985/274877906944)
  b := (1302383/274877906944)
  s := [(2199022740111/2199023255552),(-206175/4398046511104),(-5155/2199023255552)]
  L := [(4526544089077/36893488147419103232),(2715914284721/110680464442257309696),(67897500593/55340232221128654848),(-899/6917529027641081856),(-5/3458764513820540928)]
  c := (1131636022269/9223372036854775808)
  R := (-795679343318429/100000000000000)
  total := (-136255003/40000000000000)
  k := 23
  n := 32
  sFloor := (549755657967/1099511627776)
  nFloor := (1052303153889/1180591620717411303424)
  eFloor := (502589041691/590295810358705651712)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell074
