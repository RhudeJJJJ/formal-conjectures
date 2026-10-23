/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell251
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (374145/4096)
  b := (823119/8192)
  s := [(6047940560617/9223372036854775808),(-894705620389/4611686018427387904),(71440807815/2305843009213693952)]
  L := [(151151735948537949634055/151115727451828646838272),(-208923709/4398046511104),(46795997/6597069766656),(-252721/274877906944),(36343/412316860416)]
  c := (274932069627/274877906944)
  R := (4925582063/50000000000000)
  total := (989534457349/1000000000000000)
  k := 0
  n := 32
  sFloor := (568036568887/2305843009213693952)
  nFloor := 217585400161428624389813615609161751552970318347754602161040123781810966833192667914183544500387840
  eFloor := 217533280050425120999803509553899760473217346474717851325843306409399369260001337485903759612575744
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell251
