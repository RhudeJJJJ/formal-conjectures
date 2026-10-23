/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell046
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (656819/2199023255552)
  b := (1445001/4398046511104)
  s := [(1099511622051/1099511627776),(-1145/1099511627776),(-57/1099511627776)]
  L := [(301781919367957221664618793/83076749736557242056487941267521536),(857710574353/1180591620717411303424),(64327899823/1770887431076116955136),(3/73786976294838206464),(-7/110680464442257309696)]
  c := (1072144752953/295147905179352825856)
  R := (-971666303893761/100000000000000)
  total := (-144388111/500000000000000)
  k := 29
  n := 32
  sFloor := (1099511620849/2199023255552)
  nFloor := (472108386821/75557863725914323419136)
  eFloor := (1353366276263/302231454903657293676544)
}

#check "COMPACT_WITNESS_READY"
theorem checked : ComputedPolynomialCell.checks data witness=true := by decide +kernel
#check "COMPACT_CHECK_PASSED"

noncomputable section
theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u=1) :
    (witness.total : ℝ)≤∫ y : ℝ in (witness.a : ℝ)..(witness.b : ℝ),
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 9 13)
        (CoreQuotient.fused G u 9 13) ((51/26 : ℚ) : ℝ) y :=
  ComputedPolynomialCell.computed_actual_integral (51/26) 9 13 witness checked G u hd
#print axioms checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell046
