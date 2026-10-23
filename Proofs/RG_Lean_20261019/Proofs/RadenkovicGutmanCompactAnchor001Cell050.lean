/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell050
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1923295/4398046511104)
  b := (264453/549755813888)
  s := [(2199023250239/2199023255552),(-133/274877906944),(-13/549755813888)]
  L := [(1493056639073/1180591620717411303424),(895831652155/3541774862152233910272),(22395732863/1770887431076116955136),(-7/221360928884514619392),(1/110680464442257309696)]
  c := (1493056639073/1180591620717411303424)
  R := (-64026425215661/6250000000000)
  total := (-445868917/1000000000000000)
  k := 30
  n := 32
  sFloor := (2199023249123/4398046511104)
  nFloor := (173548271731/18889465931478580854784)
  eFloor := (331552592113/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell050
