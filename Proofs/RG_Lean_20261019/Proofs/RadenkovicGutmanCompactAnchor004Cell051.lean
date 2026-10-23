/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor004Cell051
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 13
def witness : ComputedPolynomialCell.Witness := {
  a := (264453/549755813888)
  b := (1163593/2199023255552)
  s := [(4398046451709/4398046511104),(-2969/1099511627776),(-149/1099511627776)]
  L := [(5561718205893/590295810358705651712),(3337024568107/1770887431076116955136),(83425451833/885443715538058477568),(-55/110680464442257309696),(-1/55340232221128654848)]
  c := (1390429551473/147573952589676412928)
  R := (-46200568130871/5000000000000)
  total := (-442154491/1000000000000000)
  k := 27
  n := 32
  sFloor := (1099511609809/2199023255552)
  nFloor := (612261969581/37778931862957161709568)
  eFloor := (438784146291/37778931862957161709568)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor004Cell051
