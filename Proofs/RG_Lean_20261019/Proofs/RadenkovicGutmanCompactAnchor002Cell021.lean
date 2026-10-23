/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell021
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (242489/8796093022208)
  b := (1066951/35184372088832)
  s := [(4398046510891/4398046511104),(-5/549755813888),(-1/1099511627776)]
  L := [(351110098241331446574287931/10633823966279326983230456482242756608),(1496863119059/226673591177742970257408),(37421346463/113336795588871485128704),(1/3541774862152233910272),(-1/7083549724304467820544)]
  c := (623696824393/18889465931478580854784)
  R := (-301674514156651/25000000000000)
  total := (-33132371/1000000000000000)
  k := 35
  n := 32
  sFloor := (2199023255423/4398046511104)
  nFloor := (932179443917/19342813113834066795298816)
  eFloor := (680793257757/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell021
