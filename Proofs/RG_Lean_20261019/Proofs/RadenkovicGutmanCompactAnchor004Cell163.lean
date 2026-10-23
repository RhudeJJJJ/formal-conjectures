/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell163
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1396107/67108864)
  b := (1535717/67108864)
  s := [(394399174855/2199023255552),(-164943456959/17592186044416),(5030878615/4398046511104)]
  L := [(4548913778854843604219/4722366482869645213696),(228155996173/13194139533312),(-16875710617/6597069766656),(175134269/824633720832),(-5956067/412316860416)]
  c := (2118253046113/2199023255552)
  R := (-37421572901/2000000000000)
  total := (-30499694471/1000000000000000)
  k := 1
  n := 32
  sFloor := (752593364085/8796093022208)
  nFloor := (555601268715/17592186044416)
  eFloor := (1605420064217/70368744177664)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell163
