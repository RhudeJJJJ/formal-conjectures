/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell248
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (281101/4096)
  b := (309211/4096)
  s := [(3563826285243/2305843009213693952),(-2108347311703/4611686018427387904),(168307471103/2305843009213693952)]
  L := [(75589690362524632242165/75557863725914323419136),(-276640015/3298534883328),(20625959/1649267441664),(-667381/412316860416),(1997/12884901888)]
  c := (549947347161/549755813888)
  R := (17416815893/100000000000000)
  total := (262851651411/200000000000000)
  k := 0
  n := 32
  sFloor := (1338980050247/2305843009213693952)
  nFloor := 135131703758443554007349306823208735349654428807005708173285249932585156844593150877906239488
  eFloor := 135074389732160449925639045586841766745981222936468236097451940555186795324026855171414818816
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell248
