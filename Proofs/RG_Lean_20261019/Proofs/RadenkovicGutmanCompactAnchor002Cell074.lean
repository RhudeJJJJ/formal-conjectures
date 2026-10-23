/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor002Cell074
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 11
def witness : ComputedPolynomialCell.Witness := {
  a := (1183985/274877906944)
  b := (1302383/274877906944)
  s := [(2199020666523/2199023255552),(-1035607/4398046511104),(-25889/2199023255552)]
  L := [(7434492546147/9223372036854775808),(4460671324939/27670116110564327424),(111515775695/13835058055282163712),(-6709/1729382256910270464),(-83/864691128455135232)]
  c := (232327892067/288230376151711744)
  R := (-350778023344923/50000000000000)
  total := (-3000958371/1000000000000000)
  k := 21
  n := 32
  sFloor := (1099510061415/2199023255552)
  nFloor := (1388953976141/1180591620717411303424)
  eFloor := (1014386777915/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor002Cell074
