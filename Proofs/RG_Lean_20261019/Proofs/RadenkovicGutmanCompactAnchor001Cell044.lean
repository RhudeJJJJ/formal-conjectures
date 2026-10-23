/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell044
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (271413/1099511627776)
  b := (1194217/4398046511104)
  s := [(2199023253859/2199023255552),(-677/4398046511104),(-17/2199023255552)]
  L := [(3805885681869/9444732965739290427392),(2283527200445/28334198897217871282176),(57088074637/14167099448608935641088),(1/1770887431076116955136),(-1/885443715538058477568)]
  c := (951471420467/2361183241434822606848)
  R := (-270402179160223/25000000000000)
  total := (-265798301/1000000000000000)
  k := 32
  n := 32
  sFloor := (2199023253503/4398046511104)
  nFloor := (884768687277/302231454903657293676544)
  eFloor := (845146277637/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell044
