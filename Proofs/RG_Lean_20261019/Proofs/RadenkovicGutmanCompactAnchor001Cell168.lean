/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell168
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1124219/33554432)
  b := (38645/1048576)
  s := [(656375082407/2199023255552),(-57426544295/8796093022208),(2728460053/2199023255552)]
  L := [(673882956633550124633/1180591620717411303424),(244557382477/26388279066624),(-7575304117/4398046511104),(285453491/1649267441664),(-3172515/274877906944)]
  c := (627602410161/1099511627776)
  R := (-14017863107947/50000000000000)
  total := (-463665880387/500000000000000)
  k := 1
  n := 32
  sFloor := (322373453193/2199023255552)
  nFloor := (1053333810103/17592186044416)
  eFloor := (124621061403/2199023255552)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell168
