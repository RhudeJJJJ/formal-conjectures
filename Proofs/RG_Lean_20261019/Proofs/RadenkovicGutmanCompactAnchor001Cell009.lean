/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell009
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1236239/140737488355328)
  b := (679931/70368744177664)
  s := [(4398046511099/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(9638498533/18889465931478580854784),(1480462596625/14507109835375550096474112),(578301491/113336795588871485128704),(1/113336795588871485128704),(-1/226673591177742970257408)]
  c := (9638498533/18889465931478580854784)
  R := (-44224781534119/3125000000000)
  total := (-2477691/200000000000000)
  k := 41
  n := 32
  sFloor := (2199023255549/4398046511104)
  nFloor := (1147237544365/309485009821345068724781056)
  eFloor := (273965261805/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell009
