/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell066
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1104679/549755813888)
  b := (607573/274877906944)
  s := [(137438946461/137438953472),(-44871/4398046511104),(-1121/2199023255552)]
  L := [(3940457410719/147573952589676412928),(788085017273/147573952589676412928),(59105881547/221360928884514619392),(-59/9223372036854775808),(1/13835058055282163712)]
  c := (1970228705359/73786976294838206464)
  R := (-435963579273137/50000000000000)
  total := (-1742309039/1000000000000000)
  k := 26
  n := 32
  sFloor := (2199023119819/4398046511104)
  nFloor := (114506642333/590295810358705651712)
  eFloor := (875029724001/4722366482869645213696)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell066
