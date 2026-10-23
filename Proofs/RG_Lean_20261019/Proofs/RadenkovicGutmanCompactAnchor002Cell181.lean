/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell181
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1940543/16777216)
  b := (533649/4194304)
  s := [(7551238113905/35184372088832),(364372556069/35184372088832),(-11335526359/17592186044416)]
  L := [(3804073645177850727325/4722366482869645213696),(-612315090905/26388279066624),(27382311721/13194139533312),(-22210603/1649267441664),(-6238225/824633720832)]
  c := (1724901042267/2199023255552)
  R := (-12142180249659/100000000000000)
  total := (-265924150311/200000000000000)
  k := 1
  n := 32
  sFloor := (471952382119/4398046511104)
  nFloor := (154033710981/68719476736)
  eFloor := (494568865565/274877906944)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell181
