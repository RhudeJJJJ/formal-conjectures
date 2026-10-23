/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell248
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (281101/4096)
  b := (309211/4096)
  s := [(3563826285243/2305843009213693952),(-2108347311703/4611686018427387904),(168307471103/2305843009213693952)]
  L := [(151179380725083292302677/151115727451828646838272),(-276640015/3298534883328),(20625959/1649267441664),(-667381/412316860416),(1997/12884901888)]
  c := (1099894694323/1099511627776)
  R := (17416815939/100000000000000)
  total := (164282282233/125000000000000)
  k := 0
  n := 32
  sFloor := (1338980050247/2305843009213693952)
  nFloor := 636717279078312396266150867553636359742047086246820433749770703398485635663921213316387636772864
  eFloor := 636447225272533865711581453170801427100735480561287615525336082602545441819109255674832204333056
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell248
