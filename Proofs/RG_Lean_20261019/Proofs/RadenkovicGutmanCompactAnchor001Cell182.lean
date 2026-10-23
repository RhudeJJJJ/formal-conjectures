/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell182
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (533649/4194304)
  b := (1174027/8388608)
  s := [(5579723135289/17592186044416),(3162276835/17592186044416),(-6013910097/8796093022208)]
  L := [(1394723130004479647099/2361183241434822606848),(40717807405/6597069766656),(1556430877/1649267441664),(-420337/6442450944),(136049/103079215104)]
  c := (1298937136311/2199023255552)
  R := (-13161673610543/50000000000000)
  total := (-3312833264393/1000000000000000)
  k := 1
  n := 32
  sFloor := (696357198991/4398046511104)
  nFloor := (364338094323/137438953472)
  eFloor := (639508775385/274877906944)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell182
