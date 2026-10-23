/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (781061/17592186044416)
  b := (859167/17592186044416)
  s := [(4398046510479/4398046511104),(-125/4398046511104),(-3/2199023255552)]
  L := [(3584569378653/37778931862957161709568),(1075369436639/56668397794435742564352),(26884201459/28334198897217871282176),(1/885443715538058477568),(-1/1770887431076116955136)]
  c := (896142344663/9444732965739290427392)
  R := (-72119934614879/6250000000000)
  total := (-51016919/1000000000000000)
  k := 34
  n := 32
  sFloor := (1099511627587/2199023255552)
  nFloor := (270465999621/2417851639229258349412352)
  eFloor := (808992440759/9671406556917033397649408)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 9)
        (CoreQuotient.fused G u 9 9) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 9 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell026
