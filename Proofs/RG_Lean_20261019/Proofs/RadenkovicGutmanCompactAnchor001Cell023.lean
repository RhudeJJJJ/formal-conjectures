/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (586823/17592186044416)
  b := (645505/17592186044416)
  s := [(2199023255521/2199023255552),(-15/4398046511104),(1/2199023255552)]
  L := [(2223917724871/302231454903657293676544),(444781271111/302231454903657293676544),(33358424785/453347182355485940514816),(1/18889465931478580854784),(-1/28334198897217871282176)]
  c := (1111958862435/151115727451828646838272)
  R := (-256351885862563/20000000000000)
  total := (-42593997/1000000000000000)
  k := 37
  n := 32
  sFloor := (1099511627757/2199023255552)
  nFloor := (1034005185061/19342813113834066795298816)
  eFloor := (246924887199/4835703278458516698824704)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell023
