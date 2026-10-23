/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell026
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (781061/17592186044416)
  b := (859167/17592186044416)
  s := [(274877906937/274877906944),(-3/549755813888)]
  L := [(2259634171460279518748877251/170141183460469231731687303715884105728),(802782295171/302231454903657293676544),(60208595051/453347182355485940514816),(-1/18889465931478580854784),(1/28334198897217871282176)]
  c := (2006958307507/151115727451828646838272)
  R := (-1252234574556397/100000000000000)
  total := (-13845487/250000000000000)
  k := 37
  n := 32
  sFloor := (549755813871/1099511627776)
  nFloor := (496858244799/4835703278458516698824704)
  eFloor := (237642592089/2417851639229258349412352)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell026
