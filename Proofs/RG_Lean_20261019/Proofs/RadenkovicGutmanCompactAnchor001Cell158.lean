/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell158
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (866875/67108864)
  b := (1907125/134217728)
  s := [(1041046466991/2199023255552),(-262306977799/8796093022208),(1254792641/549755813888)]
  L := [(7077504059149308288657/18889465931478580854784),(509767856473/17592186044416),(-15989636693/8796093022208),(69576535/1099511627776),(68685/549755813888)]
  c := (823929912777/2199023255552)
  R := (-24542077425723/50000000000000)
  total := (-610649717603/1000000000000000)
  k := 2
  n := 32
  sFloor := (980488893105/4398046511104)
  nFloor := (573105720953/70368744177664)
  eFloor := (1093326282739/140737488355328)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell158
