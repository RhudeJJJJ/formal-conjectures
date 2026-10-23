/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell139
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1133935/536870912)
  b := (38979/16777216)
  s := [(32582104139/34359738368),(-41830439643/4398046511104),(-41611179/137438953472)]
  L := [(8402313489246503501235/302231454903657293676544),(138363354019/26388279066624),(10719676259/52776558133248),(-8440435/1649267441664),(-101789/3298534883328)]
  c := (978158028941/35184372088832)
  R := (-89567151187133/50000000000000)
  total := (-368745358703/1000000000000000)
  k := 6
  n := 32
  sFloor := (1031836833105/2199023255552)
  nFloor := (120703299759/562949953421312)
  eFloor := (461173832831/2251799813685248)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell139
