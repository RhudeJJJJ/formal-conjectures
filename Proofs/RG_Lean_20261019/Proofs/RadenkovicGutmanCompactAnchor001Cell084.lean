/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell084
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1535471/137438953472)
  b := (844509/68719476736)
  s := [(2199019787953/2199023255552),(-693517/2199023255552),(-8669/549755813888)]
  L := [(267859316052394152514642453/324518553658426726783156020576256),(2283900451481/13835058055282163712),(57097078445/6917529027641081856),(-4931/864691128455135232),(-65/432345564227567616)]
  c := (951627456133/1152921504606846976)
  R := (-175092392075487/25000000000000)
  total := (-7770459671/1000000000000000)
  k := 21
  n := 32
  sFloor := (137438691235/274877906944)
  nFloor := (884915326567/147573952589676412928)
  eFloor := (422643174553/73786976294838206464)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell084
