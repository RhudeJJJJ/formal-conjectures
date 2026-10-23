/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell004
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (767609/140737488355328)
  b := (844369/140737488355328)
  s := [(2199023255547/2199023255552),(-1/2199023255552)]
  L := [(1949023106947873283921592939/1361129467683753853853498429727072845824),(4154543919985/14507109835375550096474112),(34620793393/2417851639229258349412352),(11/906694364710971881029632),(-1/151115727451828646838272)]
  c := (1731080263087/1208925819614629174706176)
  R := (-1363600384285117/100000000000000)
  total := (-231589/31250000000000)
  k := 40
  n := 32
  sFloor := (1099511627773/2199023255552)
  nFloor := (1044919607921/618970019642690137449562112)
  eFloor := (781366294833/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell004
