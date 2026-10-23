/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell059
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1133753/1099511627776)
  b := (155891/137438953472)
  s := [(4398046214353/4398046511104),(-29675/2199023255552),(-371/549755813888)]
  L := [(6817047508737/147573952589676412928),(4090217400253/442721857769029238784),(102255136195/221360928884514619392),(-343/27670116110564327424),(-7/13835058055282163712)]
  c := (26629091831/576460752303423488)
  R := (-33780827040151/4000000000000)
  total := (-865827381/1000000000000000)
  k := 25
  n := 32
  sFloor := (2199023076017/4398046511104)
  nFloor := (79599872105/1180591620717411303424)
  eFloor := (1860278953007/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell059
