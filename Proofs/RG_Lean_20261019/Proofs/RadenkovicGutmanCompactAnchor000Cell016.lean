/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (150567/8796093022208)
  b := (1324989/70368744177664)
  s := [(4398046511011/4398046511104),(-5/1099511627776)]
  L := [(1199820972795115773503491775/85070591730234615865843651857942052864),(2557559489515/906694364710971881029632),(21312889603/151115727451828646838272),(-13/56668397794435742564352),(1/9444732965739290427392)]
  c := (266413773885/18889465931478580854784)
  R := (-1249228744169369/100000000000000)
  total := (-21300691/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255495/4398046511104)
  nFloor := (643253769555/38685626227668133590597632)
  eFloor := (962020064977/77371252455336267181195264)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell016
