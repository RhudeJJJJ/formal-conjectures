/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell062
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (47157/34359738368)
  b := (829963/549755813888)
  s := [(2199023203221/2199023255552),(-20933/4398046511104),(-523/2199023255552)]
  L := [(3676518477199/295147905179352825856),(275738147675/110680464442257309696),(2297811567/18446744073709551616),(-19/13835058055282163712)]
  c := (1838259238599/147573952589676412928)
  R := (-910051046187429/100000000000000)
  total := (-1242352163/1000000000000000)
  k := 27
  n := 32
  sFloor := (2199023192231/4398046511104)
  nFloor := (854694224043/9444732965739290427392)
  eFloor := (816418632739/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell062
