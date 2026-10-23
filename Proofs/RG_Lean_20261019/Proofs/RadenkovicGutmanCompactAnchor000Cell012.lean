/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell012
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (205679/17592186044416)
  b := (904987/70368744177664)
  s := [(1099511627765/1099511627776),(-7/4398046511104),(-1/2199023255552)]
  L := [(497138026803/75557863725914323419136),(795415041939/604462909807314587353088),(59655693083/906694364710971881029632),(-1/37778931862957161709568),(1/56668397794435742564352)]
  c := (497138026803/75557863725914323419136)
  R := (-257470521781443/20000000000000)
  total := (-14994377/1000000000000000)
  k := 38
  n := 32
  sFloor := (2199023255525/4398046511104)
  nFloor := (1200335497159/154742504910672534362390528)
  eFloor := (448791319859/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell012
