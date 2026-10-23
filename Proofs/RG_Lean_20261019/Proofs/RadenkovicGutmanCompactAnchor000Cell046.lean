/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (656819/2199023255552)
  b := (1445001/4398046511104)
  s := [(2199023241429/2199023255552),(-353/274877906944),(-71/1099511627776)]
  L := [(2534886368663/590295810358705651712),(3041845097653/3541774862152233910272),(76045662371/1770887431076116955136),(-31/221360928884514619392),(1/110680464442257309696)]
  c := (1267443184331/295147905179352825856)
  R := (-963299276582731/100000000000000)
  total := (-143138559/500000000000000)
  k := 28
  n := 32
  sFloor := (2199023238463/4398046511104)
  nFloor := (47816104781/9444732965739290427392)
  eFloor := (8938939499/2361183241434822606848)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell046
