/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell002
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (158597/35184372088832)
  b := (1395653/281474976710656)
  s := [(2199023255549/2199023255552),(-3/4398046511104),(1/2199023255552)]
  L := [(4268736685369/4835703278458516698824704),(1280614949579/7253554917687775048237056),(8003805595/906694364710971881029632),(-1/56668397794435742564352),(1/113336795588871485128704)]
  c := (533592085671/604462909807314587353088)
  R := (-693893244118719/50000000000000)
  total := (-1246747/200000000000000)
  k := 41
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (797508587861/618970019642690137449562112)
  eFloor := (582439865159/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell002
