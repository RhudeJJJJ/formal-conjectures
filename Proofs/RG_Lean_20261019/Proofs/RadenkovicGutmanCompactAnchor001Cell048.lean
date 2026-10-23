/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell048
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1589501/4398046511104)
  b := (874225/2199023255552)
  s := [(2199023251923/2199023255552),(-363/1099511627776),(-9/549755813888)]
  L := [(1148169146526091356867802475/1329227995784915872903807060280344576),(305931599695/1770887431076116955136),(3824118499/442721857769029238784),(5/442721857769029238784),(-1/110680464442257309696)]
  c := (2039558116219/2361183241434822606848)
  R := (-208696955291313/20000000000000)
  total := (-93843627/250000000000000)
  k := 31
  n := 32
  sFloor := (2199023251161/4398046511104)
  nFloor := (237071907791/37778931862957161709568)
  eFloor := (905820666047/151115727451828646838272)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell048
