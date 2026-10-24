/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode196
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .times e196 e003
noncomputable def p197 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step197 : p197=NestedArithmetic.mul p196 p003 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e196) (NestedArithmetic.compile e003)=p197
  rw [h196,h003]
  exact step197.symm
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
