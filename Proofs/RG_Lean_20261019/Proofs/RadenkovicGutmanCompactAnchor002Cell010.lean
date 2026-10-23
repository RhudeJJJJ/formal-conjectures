/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell010
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (679931/70368744177664)
  b := (186981/17592186044416)
  s := [(4398046511077/4398046511104),(-3/4398046511104),(-1/2199023255552)]
  L := [(4903646249011/1208925819614629174706176),(980727807403/1208925819614629174706176),(73554477361/1813388729421943762059264),(1/75557863725914323419136),(-1/113336795588871485128704)]
  c := (306477890563/75557863725914323419136)
  R := (-1311538713401459/100000000000000)
  total := (-6312911/500000000000000)
  k := 38
  n := 32
  sFloor := (137438953471/274877906944)
  nFloor := (229031460809/38685626227668133590597632)
  eFloor := (334534461901/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell010
