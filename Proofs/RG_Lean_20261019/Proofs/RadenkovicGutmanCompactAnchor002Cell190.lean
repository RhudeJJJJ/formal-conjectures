/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell190
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (71495/262144)
  b := (157289/524288)
  s := [(4484969462067/17592186044416),(-38674208835/8796093022208),(-860127723/1099511627776)]
  L := [(1772607362869727433859/2361183241434822606848),(405961822655/26388279066624),(23828438597/13194139533312),(-432155075/1649267441664),(15470779/824633720832)]
  c := (825434626485/1099511627776)
  R := (-1791945736599/12500000000000)
  total := (-3761326579639/1000000000000000)
  k := 1
  n := 32
  sFloor := (1098464750207/8796093022208)
  nFloor := (983432362761/4294967296)
  eFloor := (1555460515099/8589934592)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell190
