/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell147
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (607671/134217728)
  b := (334219/67108864)
  s := [(7170231620823/8796093022208),(-117361417775/4398046511104),(423237795/2199023255552)]
  L := [(128899838808068491442655/1208925819614629174706176),(111802324241/6597069766656),(2368274771/13194139533312),(-118723063/3298534883328),(569945/412316860416)]
  c := (1875739527285/17592186044416)
  R := (-111922591624783/100000000000000)
  total := (-244762941417/500000000000000)
  k := 4
  n := 32
  sFloor := (1734300434113/4398046511104)
  nFloor := (1110944198267/1125899906842624)
  eFloor := (1061006609605/1125899906842624)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 10)
        (CoreQuotient.fused G u 9 10) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 10 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell147
