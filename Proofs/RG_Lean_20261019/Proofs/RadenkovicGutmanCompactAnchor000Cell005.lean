/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell005
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (844369/140737488355328)
  b := (928805/140737488355328)
  s := [(1099511627773/1099511627776),(-1/2199023255552)]
  L := [(18866503456190224157220057615/10889035741470030830827987437816582766592),(1675664261669/4835703278458516698824704),(125673479947/7253554917687775048237056),(9/302231454903657293676544),(-7/453347182355485940514816)]
  c := (2094602653123/1208925819614629174706176)
  R := (-1354069472893099/100000000000000)
  total := (-8094751/1000000000000000)
  k := 40
  n := 32
  sFloor := (2199023255545/4398046511104)
  nFloor := (1264350030281/618970019642690137449562112)
  eFloor := (945451201263/618970019642690137449562112)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell005
