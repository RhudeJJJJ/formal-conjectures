/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell003
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1395653/281474976710656)
  b := (767609/140737488355328)
  s := [(4398046511097/4398046511104),(1/4398046511104),(-1/2199023255552)]
  L := [(681281687363031790087304563/680564733841876926926749214863536422912),(2904472280525/14507109835375550096474112),(24203883621/2417851639229258349412352),(13/906694364710971881029632),(-1/151115727451828646838272)]
  c := (1210199384905/1208925819614629174706176)
  R := (-276299682019201/20000000000000)
  total := (-1365189/200000000000000)
  k := 40
  n := 32
  sFloor := (549755813887/1099511627776)
  nFloor := (2131597528099/1237940039285380274899124224)
  eFloor := (763816183323/618970019642690137449562112)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell003
