/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell055
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1548741/2199023255552)
  b := (851807/1099511627776)
  s := [(4398046483543/4398046511104),(-689/549755813888),(-69/1099511627776)]
  L := [(3872594805751/1180591620717411303424),(2323540364309/3541774862152233910272),(58088094913/1770887431076116955136),(-17/221360928884514619392),(-1/110680464442257309696)]
  c := (1936297402875/590295810358705651712)
  R := (-488383918711593/50000000000000)
  total := (-342254881/500000000000000)
  k := 29
  n := 32
  sFloor := (2199023238877/4398046511104)
  nFloor := (900276815931/37778931862957161709568)
  eFloor := (859959909031/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell055
