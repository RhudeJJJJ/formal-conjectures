/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (150567/8796093022208)
  b := (1324989/70368744177664)
  s := [(2199023255511/2199023255552),(-19/4398046511104),(1/2199023255552)]
  L := [(240463432613/18889465931478580854784),(2308437454295/906694364710971881029632),(19236882937/151115727451828646838272),(13/56668397794435742564352),(-1/9444732965739290427392)]
  c := (240463432613/18889465931478580854784)
  R := (-250870574938513/20000000000000)
  total := (-21388403/1000000000000000)
  k := 37
  n := 32
  sFloor := (1099511627751/2199023255552)
  nFloor := (1437589932299/77371252455336267181195264)
  eFloor := (1049906796073/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell016
