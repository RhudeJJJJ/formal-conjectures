/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell035
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1841697/17592186044416)
  b := (1012933/8796093022208)
  s := [(4398046510495/4398046511104),(-31/1099511627776),(-1/1099511627776)]
  L := [(96338668764416530214944657/1329227995784915872903807060280344576),(3285719091671/226673591177742970257408),(82142664815/113336795588871485128704),(43/14167099448608935641088),(-11/7083549724304467820544)]
  c := (1369054825267/18889465931478580854784)
  R := (-583693741308201/50000000000000)
  total := (-121704657/1000000000000000)
  k := 34
  n := 32
  sFloor := (2199023255183/4398046511104)
  nFloor := (636538740765/1208925819614629174706176)
  eFloor := (608032760501/1208925819614629174706176)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell035
