/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell016
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (150567/8796093022208)
  b := (1324989/70368744177664)
  s := [(1099511627757/1099511627776),(-3/1099511627776),(-1/1099511627776)]
  L := [(3605799555781/302231454903657293676544),(721156318921/302231454903657293676544),(54086454493/453347182355485940514816),(1/18889465931478580854784),(-1/28334198897217871282176)]
  c := (901449888945/75557863725914323419136)
  R := (-62879788577043/5000000000000)
  total := (-21443913/1000000000000000)
  k := 37
  n := 32
  sFloor := (1099511627753/2199023255552)
  nFloor := (198472290907/9671406556917033397649408)
  eFloor := (1137898469013/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell016
