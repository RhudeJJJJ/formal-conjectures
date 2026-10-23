/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell191
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (157289/524288)
  b := (1384143/4194304)
  s := [(2220412722359/8796093022208),(-130087085045/17592186044416),(-4278046943/8796093022208)]
  L := [(901431791123456945867/1180591620717411303424),(188849286055/8796093022208),(15523556305/13194139533312),(-130027925/549755813888),(16093763/824633720832)]
  c := (839523776549/1099511627776)
  R := (-6744664676523/50000000000000)
  total := (-3831434459543/1000000000000000)
  k := 1
  n := 32
  sFloor := (2151091132893/17592186044416)
  nFloor := (237375919985/268435456)
  eFloor := (742267251271/1073741824)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell191
