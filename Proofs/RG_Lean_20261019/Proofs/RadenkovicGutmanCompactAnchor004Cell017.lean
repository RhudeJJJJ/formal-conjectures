/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell017
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1324989/70368744177664)
  b := (1457487/70368744177664)
  s := [(1099511627753/1099511627776),(-17/4398046511104),(-1/2199023255552)]
  L := [(1090753377759/75557863725914323419136),(2617790325103/906694364710971881029632),(65444313553/453347182355485940514816),(5/56668397794435742564352),(-1/28334198897217871282176)]
  c := (1090753377759/75557863725914323419136)
  R := (-1248064798843991/100000000000000)
  total := (-23408791/1000000000000000)
  k := 37
  n := 32
  sFloor := (274877906937/549755813888)
  nFloor := (1921210036001/77371252455336267181195264)
  eFloor := (1376855900531/77371252455336267181195264)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell017
