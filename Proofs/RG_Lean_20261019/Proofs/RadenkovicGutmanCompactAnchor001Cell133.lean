/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell133
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (320039/268435456)
  b := (1408171/1073741824)
  s := [(4321264449765/4398046511104),(-14933935035/4398046511104),(-325965595/2199023255552)]
  L := [(178320138514474463194655/19342813113834066795298816),(763525494583/422212465065984),(35256936997/422212465065984),(-8709041/13194139533312),(-320713/26388279066624)]
  c := (648724884793/70368744177664)
  R := (-58581196853861/25000000000000)
  total := (-13685822751/50000000000000)
  k := 7
  n := 32
  sFloor := (1076419645885/2199023255552)
  nFloor := (1230362263443/18014398509481984)
  eFloor := (293812220131/4503599627370496)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell133
