/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell181
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1940543/16777216)
  b := (533649/4194304)
  s := [(5564741513903/17592186044416),(13507104651/8796093022208),(-3008146979/4398046511104)]
  L := [(5533719515507781077885/9444732965739290427392),(17181711331/4398046511104),(2031160699/2199023255552),(-12871775/274877906944),(-86487/137438953472)]
  c := (1288419476595/2199023255552)
  R := (-6682462897291/25000000000000)
  total := (-383694166859/125000000000000)
  k := 1
  n := 32
  sFloor := (1391185378475/8796093022208)
  nFloor := (502507265183/274877906944)
  eFloor := (445458561695/274877906944)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell181
