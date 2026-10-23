/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell061
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (21435/17179869184)
  b := (47157/34359738368)
  s := [(2199023055767/2199023255552),(-39957/2199023255552),(-999/1099511627776)]
  L := [(10531704725985327063005078277/166153499473114484112975882535043072),(2806209597121/221360928884514619392),(70155213751/110680464442257309696),(-313/13835058055282163712),(-7/6917529027641081856)]
  c := (584627053767/9223372036854775808)
  R := (-414350810233139/50000000000000)
  total := (-513957943/500000000000000)
  k := 24
  n := 32
  sFloor := (549755753453/1099511627776)
  nFloor := (1029739160589/9444732965739290427392)
  eFloor := (46123354967/590295810358705651712)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell061
