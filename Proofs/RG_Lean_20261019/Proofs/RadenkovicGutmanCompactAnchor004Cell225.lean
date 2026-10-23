/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell225
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (2009161/262144)
  b := (552519/65536)
  s := [(584775224857/562949953421312),(-1326940922367/4503599627370496),(101646377025/2251799813685248)]
  L := [(9727194773738260966985/9444732965739290427392),(-71328327929/13194139533312),(1565596727/2199023255552),(-65399359/824633720832),(901161/137438953472)]
  c := (281788322809/274877906944)
  R := (31036420509/2500000000000)
  total := (323965361759/31250000000000)
  k := 0
  n := 32
  sFloor := (1777276815269/4503599627370496)
  nFloor := 46539143504784914992956793841773999560012595200
  eFloor := 45093941051086336538846918645057806846669094912
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell225
