/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell006
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (928805/140737488355328)
  b := (2043371/281474976710656)
  s := [(2199023255545/2199023255552),(-5/4398046511104),(1/2199023255552)]
  L := [(2534464298549/1208925819614629174706176),(3041357158283/7253554917687775048237056),(25344642961/1208925819614629174706176),(13/453347182355485940514816),(-1/75557863725914323419136)]
  c := (633616074637/302231454903657293676544)
  R := (-134453855181137/10000000000000)
  total := (-8841413/1000000000000000)
  k := 39
  n := 32
  sFloor := (2199023255543/4398046511104)
  nFloor := (1529860571809/618970019642690137449562112)
  eFloor := (1143993736497/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell006
