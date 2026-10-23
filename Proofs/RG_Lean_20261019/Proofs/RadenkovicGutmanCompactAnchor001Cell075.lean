/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedPolynomialCell

namespace Gebendorfer.RadenkovicGutman.CompactAnchor001Cell075
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (51/26) 9 10
def witness : ComputedPolynomialCell.Witness := {
  a := (1302383/274877906944)
  b := (1432621/274877906944)
  s := [(4398045263737/4398046511104),(-124735/2199023255552),(-3119/1099511627776)]
  L := [(2738556923099/18446744073709551616),(821564928533/27670116110564327424),(10269525155/6917529027641081856),(-5/27021597764222976),(-1/216172782113783808)]
  c := (1369278461549/9223372036854775808)
  R := (-786148366432487/100000000000000)
  total := (-3701860233/1000000000000000)
  k := 23
  n := 32
  sFloor := (2199022500895/4398046511104)
  nFloor := (636642919509/590295810358705651712)
  eFloor := (1216264547427/1180591620717411303424)
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
end Gebendorfer.RadenkovicGutman.CompactAnchor001Cell075
