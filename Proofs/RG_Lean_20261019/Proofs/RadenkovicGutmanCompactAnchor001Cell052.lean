/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell052
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1163593/2199023255552)
  b := (79997/137438953472)
  s := [(2199023247773/2199023255552),(-3113/4398046511104),(-77/2199023255552)]
  L := [(4371964875715/2361183241434822606848),(655793038021/1770887431076116955136),(32789566877/1770887431076116955136),(-11/221360928884514619392),(1/110680464442257309696)]
  c := (2185982437857/1180591620717411303424)
  R := (-502680404186569/50000000000000)
  total := (-529414727/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023246139/4398046511104)
  nFloor := (508183634387/37778931862957161709568)
  eFloor := (485425753797/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell052
