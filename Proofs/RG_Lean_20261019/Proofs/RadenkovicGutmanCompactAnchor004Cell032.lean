/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell032
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1383695/17592186044416)
  b := (95129/1099511627776)
  s := [(1099511627379/1099511627776),(-159/2199023255552),(-1/274877906944)]
  L := [(2379100343525/9444732965739290427392),(1427455047415/28334198897217871282176),(8921561809/3541774862152233910272),(-5/885443715538058477568),(1/442721857769029238784)]
  c := (594775085881/2361183241434822606848)
  R := (-110510003278247/10000000000000)
  total := (-43269721/500000000000000)
  k := 32
  n := 32
  sFloor := (2199023254591/4398046511104)
  nFloor := (2095226818193/4835703278458516698824704)
  eFloor := (750783452491/2417851639229258349412352)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell032
