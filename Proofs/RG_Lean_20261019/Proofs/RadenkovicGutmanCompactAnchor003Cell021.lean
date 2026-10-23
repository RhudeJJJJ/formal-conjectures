/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (242489/8796093022208)
  b := (1066951/35184372088832)
  s := [(1099511627765/1099511627776),(-7/4398046511104),(-1/2199023255552)]
  L := [(193442782011/37778931862957161709568),(619013073285/604462909807314587353088),(46425693301/906694364710971881029632),(1/37778931862957161709568),(-1/56668397794435742564352)]
  c := (193442782011/37778931862957161709568)
  R := (-1299889546825457/100000000000000)
  total := (-111567/3125000000000)
  k := 38
  n := 32
  sFloor := (2199023255525/4398046511104)
  nFloor := (1532486502031/38685626227668133590597632)
  eFloor := (732973777725/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell021
