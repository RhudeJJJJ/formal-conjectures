/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell153
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (269131/33554432)
  b := (74011/8388608)
  s := [(5560362336387/8796093022208),(-77008940973/2199023255552),(229399189/137438953472)]
  L := [(4459453757647912450953/18889465931478580854784),(1455419660297/52776558133248),(-19755389305/26388279066624),(-91792043/3298534883328),(6911773/1649267441664)]
  c := (2076594977475/8796093022208)
  R := (-72178906294691/100000000000000)
  total := (-4454118489/8000000000000)
  k := 3
  n := 32
  sFloor := (1316752030147/4398046511104)
  nFloor := (218822079407/70368744177664)
  eFloor := (417815253479/140737488355328)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell153
