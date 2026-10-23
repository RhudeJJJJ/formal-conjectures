/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell049
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (874225/2199023255552)
  b := (1923295/4398046511104)
  s := [(17179869149/17179869184),(-897/2199023255552),(-11/549755813888)]
  L := [(88463616876795121394552905/83076749736557242056487941267521536),(3017144650135/14167099448608935641088),(75428615489/7083549724304467820544),(11/885443715538058477568),(-5/442721857769029238784)]
  c := (1257143607017/1180591620717411303424)
  R := (-32281936491169/3125000000000)
  total := (-408755039/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023250131/4398046511104)
  nFloor := (1244913090807/151115727451828646838272)
  eFloor := (297715069561/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell049
