/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor003Cell014
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 12
def witness : ComputedPolynomialCell.Witness := {
  a := (995485/70368744177664)
  b := (1095033/70368744177664)
  s := [(1099511627773/1099511627776),(-1/2199023255552)]
  L := [(1630076136325/1208925819614629174706176),(1304054359163/4835703278458516698824704),(97803585811/7253554917687775048237056),(-7/302231454903657293676544),(5/453347182355485940514816)]
  c := (1630076136325/1208925819614629174706176)
  R := (-1366606330286871/100000000000000)
  total := (-3852877/200000000000000)
  k := 40
  n := 32
  sFloor := (2199023255545/4398046511104)
  nFloor := (807108712655/77371252455336267181195264)
  eFloor := (193016226037/19342813113834066795298816)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor003Cell014
