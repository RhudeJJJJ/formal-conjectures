/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell000
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1/268435456)
  b := (1153433/281474976710656)
  s := [(4398046511103/4398046511104)]
  L := [(3550375537501/38685626227668133590597632),(2130213133241/116056878683004400771792896),(53255023631/58028439341502200385896448),(-5/7253554917687775048237056),(1/3626777458843887524118528)]
  c := (887593884375/9671406556917033397649408)
  R := (-750485896214077/50000000000000)
  total := (-1393373/250000000000000)
  k := 44
  n := 32
  sFloor := (2199023255551/4398046511104)
  nFloor := (825369273687/1237940039285380274899124224)
  eFloor := (788406935467/1237940039285380274899124224)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell000
