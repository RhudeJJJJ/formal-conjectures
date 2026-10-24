/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode117
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e117 e036
noncomputable def p172 : NestedHorner.Poly 3 := [[[-2]]]
theorem step172 : p172=NestedArithmetic.mul p117 p036 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e117) (NestedArithmetic.compile e036)=p172
  rw [h117,h036]
  exact step172.symm
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
