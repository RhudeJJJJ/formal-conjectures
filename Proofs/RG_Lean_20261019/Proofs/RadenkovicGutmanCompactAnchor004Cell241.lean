/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell241
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1153997/32768)
  b := (317349/8192)
  s := [(3288668251495/288230376151711744),(-971266483897/288230376151711744),(77416581089/144115188075855872)]
  L := [(4729851329750534309305/4722366482869645213696),(-4139842343/13194139533312),(306648763/6597069766656),(-4926397/824633720832),(234437/412316860416)]
  c := (550477253697/549755813888)
  R := (13114310661/20000000000000)
  total := (253768001219/100000000000000)
  k := 0
  n := 32
  sFloor := (154514683111/36028797018963968)
  nFloor := 562921657456282286756425556783175108335216768504541230293236353309641655682334720
  eFloor := 562018025553218925313167737584587493841600475635533062591175696098279578845315072
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell241
