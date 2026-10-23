/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell219
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (141765/32768)
  b := (311883/65536)
  s := [(2860170123857/562949953421312),(-187510341541/140737488355328),(26593641655/140737488355328)]
  L := [(40737273859370172343603/37778931862957161709568),(-156543653737/13194139533312),(7856049889/6597069766656),(-70139975/824633720832),(1353791/412316860416)]
  c := (1173784838985/1099511627776)
  R := (1634183160173/50000000000000)
  total := (3797533837497/250000000000000)
  k := 0
  n := 32
  sFloor := (277062915539/140737488355328)
  nFloor := 72906593935474541159604172095488
  eFloor := 66928556495149586418543506751488
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell219
