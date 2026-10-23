/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell053
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (79997/137438953472)
  b := (1407947/2199023255552)
  s := [(4398046416549/4398046511104),(-18911/4398046511104),(-473/2199023255552)]
  L := [(4891213236817599854714022415/332306998946228968225951765070086144),(2606557895695/885443715538058477568),(65163839879/442721857769029238784),(-79/55340232221128654848),(1/27670116110564327424)]
  c := (1086067510773/73786976294838206464)
  R := (-901706470841611/100000000000000)
  total := (-522024243/1000000000000000)
  k := 27
  n := 32
  sFloor := (1099511599173/2199023255552)
  nFloor := (811620158117/37778931862957161709568)
  eFloor := (296372943597/18889465931478580854784)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell053
