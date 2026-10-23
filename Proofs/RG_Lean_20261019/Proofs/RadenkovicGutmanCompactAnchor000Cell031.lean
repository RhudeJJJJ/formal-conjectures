/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell031
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1257905/17592186044416)
  b := (1383695/17592186044416)
  s := [(4398046509485/4398046511104),(-81/1099511627776),(-1/274877906944)]
  L := [(4648713433651/18889465931478580854784),(929738990787/18889465931478580854784),(69730147009/28334198897217871282176),(1/1180591620717411303424),(-1/1770887431076116955136)]
  c := (290544589603/1180591620717411303424)
  R := (-221252797451273/20000000000000)
  total := (-78755447/1000000000000000)
  k := 32
  n := 32
  sFloor := (549755813643/1099511627776)
  nFloor := (1403034834323/4835703278458516698824704)
  eFloor := (524578217169/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell031
