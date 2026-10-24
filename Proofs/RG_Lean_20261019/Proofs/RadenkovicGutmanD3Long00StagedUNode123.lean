/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode122
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e123 : NestedArithmetic.Expr 3 := .times e122 e003
noncomputable def p123 : NestedHorner.Poly 3 := [[[]],[[0]],[[3]]]
theorem step123 : p123=NestedArithmetic.mul p122 p003 := by decide +kernel
#print axioms step123
theorem h123 : NestedArithmetic.compile e123=p123 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e122) (NestedArithmetic.compile e003)=p123
  rw [h122,h003]
  exact step123.symm
#print axioms h123
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
