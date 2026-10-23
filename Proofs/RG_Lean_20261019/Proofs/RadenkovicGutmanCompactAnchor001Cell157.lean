/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell157
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1576137/134217728)
  b := (866875/67108864)
  s := [(2211234546373/4398046511104),(-139034118743/4398046511104),(618281647/274877906944)]
  L := [(6550665085523085952367/18889465931478580854784),(1556030769119/52776558133248),(-14389839227/8796093022208),(137461615/3298534883328),(832863/549755813888)]
  c := (1525195568223/4398046511104)
  R := (-13237972803679/25000000000000)
  total := (-598390138369/1000000000000000)
  k := 2
  n := 32
  sFloor := (1041046466991/4398046511104)
  nFloor := (944691506349/140737488355328)
  eFloor := (901325198613/140737488355328)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell157
