/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell130
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1923603/2147483648)
  b := (1057981/1073741824)
  s := [(2177086878039/2199023255552),(-4318160171/2199023255552),(-50032545/549755813888)]
  L := [(406029085895987765775351/77371252455336267181195264),(584368985577/562949953421312),(41909922569/844424930131968),(-7782245/35184372088832),(-247601/52776558133248)]
  c := (92320325597/17592186044416)
  R := (-32812161113169/12500000000000)
  total := (-9233776647/40000000000000)
  k := 8
  n := 32
  sFloor := (271571073461/549755813888)
  nFloor := (694468462605/18014398509481984)
  eFloor := (663363662263/18014398509481984)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell130
