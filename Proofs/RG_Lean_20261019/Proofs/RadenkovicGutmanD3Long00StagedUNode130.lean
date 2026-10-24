/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode129
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e130 : NestedArithmetic.Expr 3 := .times e129 e003
noncomputable def p130 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]]]
theorem step130 : p130=NestedArithmetic.mul p129 p003 := by decide +kernel
#print axioms step130
theorem h130 : NestedArithmetic.compile e130=p130 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e129) (NestedArithmetic.compile e003)=p130
  rw [h129,h003]
  exact step130.symm
#print axioms h130
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
