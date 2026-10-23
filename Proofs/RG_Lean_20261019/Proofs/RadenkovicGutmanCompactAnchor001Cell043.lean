/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (986957/4398046511104)
  b := (271413/1099511627776)
  s := [(4398046508305/4398046511104),(-557/4398046511104),(-15/2199023255552)]
  L := [(3145364124215/9444732965739290427392),(235900636013/3541774862152233910272),(47179792429/14167099448608935641088),(1/885443715538058477568),(-1/885443715538058477568)]
  c := (1572682062107/4722366482869645213696)
  R := (-545569835068313/50000000000000)
  total := (-243772519/1000000000000000)
  k := 32
  n := 32
  sFloor := (2199023253859/4398046511104)
  nFloor := (91401841759/37778931862957161709568)
  eFloor := (698468898755/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell043
