/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell173
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (905281/16777216)
  b := (995809/16777216)
  s := [(2802832150431/17592186044416),(83684684865/17592186044416),(3073033471/8796093022208)]
  L := [(4569088513975747939341/4722366482869645213696),(-107801969503/6597069766656),(-859534511/1099511627776),(61622383/412316860416),(-720397/68719476736)]
  c := (2090300180389/2199023255552)
  R := (-1267640109637/50000000000000)
  total := (-3517839391/31250000000000)
  k := 1
  n := 32
  sFloor := (1401416075215/17592186044416)
  nFloor := (586258295529/2199023255552)
  eFloor := (878767963679/4398046511104)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell173
