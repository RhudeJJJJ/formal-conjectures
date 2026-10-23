/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell098
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1457727/34359738368)
  b := (1603499/34359738368)
  s := [(4397946503441/4398046511104),(-5000179/1099511627776),(-124983/549755813888)]
  L := [(3430725879319/288230376151711744),(2058374230247/864691128455135232),(51453967547/432345564227567616),(-64259/54043195528445952),(-803/27021597764222976)]
  c := (1715362939659/144115188075855872)
  R := (-141734293639211/25000000000000)
  total := (-476941701/20000000000000)
  k := 17
  n := 32
  sFloor := (1099481375715/2199023255552)
  nFloor := (99696740139/1152921504606846976)
  eFloor := (761856324545/9223372036854775808)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell098
