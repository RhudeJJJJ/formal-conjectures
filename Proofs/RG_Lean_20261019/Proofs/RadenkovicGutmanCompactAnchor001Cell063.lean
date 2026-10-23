/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell063
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (829963/549755813888)
  b := (912959/549755813888)
  s := [(4398046384463/4398046511104),(-25329/4398046511104),(-633/2199023255552)]
  L := [(4448585188999/295147905179352825856),(889713793677/295147905179352825856),(22242761617/147573952589676412928),(-33/18446744073709551616),(-1/9223372036854775808)]
  c := (1112146297249/73786976294838206464)
  R := (-900520052578937/100000000000000)
  total := (-1352196909/1000000000000000)
  k := 26
  n := 32
  sFloor := (1099511589467/2199023255552)
  nFloor := (1034179512709/9444732965739290427392)
  eFloor := (987866069547/9444732965739290427392)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell063
