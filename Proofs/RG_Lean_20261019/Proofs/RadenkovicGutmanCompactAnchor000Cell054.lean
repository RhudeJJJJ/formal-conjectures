/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell054
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1407947/2199023255552)
  b := (1548741/2199023255552)
  s := [(1099511595329/1099511627776),(-25957/4398046511104),(-649/2199023255552)]
  L := [(2911921704045/147573952589676412928),(873572141735/221360928884514619392),(5459798075/27670116110564327424),(-13/6917529027641081856),(-1/3458764513820540928)]
  c := (727980426011/36893488147419103232)
  R := (-443525668474059/50000000000000)
  total := (-282420793/500000000000000)
  k := 26
  n := 32
  sFloor := (1099511588515/2199023255552)
  nFloor := (219712817607/9444732965739290427392)
  eFloor := (1314368599615/75557863725914323419136)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell054
