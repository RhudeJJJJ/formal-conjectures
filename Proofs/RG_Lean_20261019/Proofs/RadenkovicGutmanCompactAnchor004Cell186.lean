/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell186
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (390657/2097152)
  b := (859445/4194304)
  s := [(4601981870175/17592186044416),(15909416655/4398046511104),(-1275073861/1099511627776)]
  L := [(212191695478745174815/295147905179352825856),(-45670801529/13194139533312),(18855509023/6597069766656),(-200640937/824633720832),(4871201/412316860416)]
  c := (1578192957313/2199023255552)
  R := (-16586639620753/100000000000000)
  total := (-123372745947/40000000000000)
  k := 1
  n := 32
  sFloor := (1150495467543/8796093022208)
  nFloor := (967308144345/34359738368)
  eFloor := (787504920027/34359738368)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell186
