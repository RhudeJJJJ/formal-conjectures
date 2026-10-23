/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor000Cell047
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 9
def witness : ComputedPolynomialCell.Witness := {
  a := (1445001/4398046511104)
  b := (1589501/4398046511104)
  s := [(2199023238463/2199023255552),(-6835/4398046511104),(-171/2199023255552)]
  L := [(6134418211303/1180591620717411303424),(3680648350453/3541774862152233910272),(92016142211/1770887431076116955136),(-43/221360928884514619392),(1/110680464442257309696)]
  c := (1533604552825/295147905179352825856)
  R := (-953768314034273/100000000000000)
  total := (-311774901/1000000000000000)
  k := 28
  n := 32
  sFloor := (1099511617437/2199023255552)
  nFloor := (115714845443/18889465931478580854784)
  eFloor := (21632209635/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor000Cell047
