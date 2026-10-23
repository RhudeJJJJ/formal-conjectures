/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell028
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (945083/17592186044416)
  b := (1039591/17592186044416)
  s := [(2199023255149/2199023255552),(-163/4398046511104),(-3/2199023255552)]
  L := [(1333334591193762109675629699/10633823966279326983230456482242756608),(2775551369/110680464442257309696),(17763472339/14167099448608935641088),(1/442721857769029238784),(-1/885443715538058477568)]
  c := (1184239010137/9444732965739290427392)
  R := (-1139981134109411/100000000000000)
  total := (-60981541/1000000000000000)
  k := 33
  n := 32
  sFloor := (274877906883/549755813888)
  nFloor := (442491936351/2417851639229258349412352)
  eFloor := (1292650374755/9671406556917033397649408)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell028
