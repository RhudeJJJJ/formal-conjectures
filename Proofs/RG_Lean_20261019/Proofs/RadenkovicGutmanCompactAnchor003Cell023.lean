/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell023
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (586823/17592186044416)
  b := (645505/17592186044416)
  s := [(68719476735/68719476736),(-11/4398046511104),(-1/2199023255552)]
  L := [(4531507365455/604462909807314587353088),(906296839815/604462909807314587353088),(67971915481/906694364710971881029632),(1/37778931862957161709568),(-1/56668397794435742564352)]
  c := (1132876841363/151115727451828646838272)
  R := (-1280827575620319/100000000000000)
  total := (-42562913/1000000000000000)
  k := 37
  n := 32
  sFloor := (2199023255513/4398046511104)
  nFloor := (560927645443/9671406556917033397649408)
  eFloor := (536572759063/9671406556917033397649408)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 12)
        (CoreQuotient.fused G u 9 12) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 12 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell023
