/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode018
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e018 e002
noncomputable def p043 : NestedHorner.Poly 3 := [[[3]],[[0]],[[2]]]
theorem step043 : p043=NestedHorner.add p018 p002 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := by
  change NestedHorner.add (NestedArithmetic.compile e018) (NestedArithmetic.compile e002)=p043
  rw [h018,h002]
  exact step043.symm
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
