/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell042
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (448617/2199023255552)
  b := (986957/4398046511104)
  s := [(4398046508791/4398046511104),(-231/2199023255552),(-3/549755813888)]
  L := [(182921903171596339549661209/664613997892457936451903530140172288),(1559678999935/28334198897217871282176),(12997267005/4722366482869645213696),(11/1770887431076116955136),(-1/295147905179352825856)]
  c := (1299738295099/4722366482869645213696)
  R := (-1100670647582411/100000000000000)
  total := (-223556433/1000000000000000)
  k := 32
  n := 32
  sFloor := (274877906769/549755813888)
  nFloor := (604310187417/302231454903657293676544)
  eFloor := (1154494983329/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell042
