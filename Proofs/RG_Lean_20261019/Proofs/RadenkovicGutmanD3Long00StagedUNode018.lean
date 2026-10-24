/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode017
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e018 : NestedArithmetic.Expr 3 := .times e017 e003
noncomputable def p018 : NestedHorner.Poly 3 := [[[]],[[0]],[[2]]]
theorem step018 : p018=NestedArithmetic.mul p017 p003 := by decide +kernel
#print axioms step018
theorem h018 : NestedArithmetic.compile e018=p018 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e017) (NestedArithmetic.compile e003)=p018
  rw [h017,h003]
  exact step018.symm
#print axioms h018
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
