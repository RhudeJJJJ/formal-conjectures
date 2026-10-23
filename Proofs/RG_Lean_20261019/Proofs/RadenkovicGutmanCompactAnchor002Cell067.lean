/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell067
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (607573/274877906944)
  b := (334165/137438953472)
  s := [(4398045147551/4398046511104),(-272711/4398046511104),(-6817/2199023255552)]
  L := [(68882048043022287084093721/324518553658426726783156020576256),(2349282321235/55340232221128654848),(19577231183/9223372036854775808),(-229/864691128455135232),(-5/576460752303423488)]
  c := (1957745554449/9223372036854775808)
  R := (-384136441886167/50000000000000)
  total := (-67497393/40000000000000)
  k := 23
  n := 32
  sFloor := (2199022430603/4398046511104)
  nFloor := (1463027122763/4722366482869645213696)
  eFloor := (534242096661/2361183241434822606848)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 11)
        (CoreQuotient.fused G u 9 11) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 11 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell067
