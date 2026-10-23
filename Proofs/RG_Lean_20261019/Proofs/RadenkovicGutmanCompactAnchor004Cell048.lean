/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell048
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (1589501/4398046511104)
  b := (874225/2199023255552)
  s := [(4398046477577/4398046511104),(-419/274877906944),(-21/274877906944)]
  L := [(110459590556579645572950877/20769187434139310514121985316880384),(470914295383/442721857769029238784),(3924258505/73786976294838206464),(5/110680464442257309696),(-1/9223372036854775808)]
  c := (392431298325/73786976294838206464)
  R := (-952604329711139/100000000000000)
  total := (-342529571/1000000000000000)
  k := 28
  n := 32
  sFloor := (549755808817/1099511627776)
  nFloor := (345606518409/37778931862957161709568)
  eFloor := (1981461121763/302231454903657293676544)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell048
