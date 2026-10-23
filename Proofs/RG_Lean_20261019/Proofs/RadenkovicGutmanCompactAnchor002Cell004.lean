/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell004
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (767609/140737488355328)
  b := (844369/140737488355328)
  s := [(4398046511095/4398046511104),(-1/2199023255552)]
  L := [(6249849564751/4835703278458516698824704),(3749865772207/14507109835375550096474112),(31248515037/2417851639229258349412352),(11/906694364710971881029632),(-1/151115727451828646838272)]
  c := (1562462391187/1208925819614629174706176)
  R := (-1368724514808433/100000000000000)
  total := (-1487759/200000000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (1167630863205/618970019642690137449562112)
  eFloor := (1705498280199/1237940039285380274899124224)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell004
