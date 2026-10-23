/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell043
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (986957/4398046511104)
  b := (271413/1099511627776)
  s := [(549755812131/549755813888),(-2809/4398046511104),(-71/2199023255552)]
  L := [(1291504496653/590295810358705651712),(774897199453/1770887431076116955136),(19372292351/885443715538058477568),(-7/110680464442257309696),(1/55340232221128654848)]
  c := (1291504496653/590295810358705651712)
  R := (-19940326527431/2000000000000)
  total := (-111325317/500000000000000)
  k := 29
  n := 32
  sFloor := (274877905881/549755813888)
  nFloor := (965143560377/302231454903657293676544)
  eFloor := (1409735503095/604462909807314587353088)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell043
