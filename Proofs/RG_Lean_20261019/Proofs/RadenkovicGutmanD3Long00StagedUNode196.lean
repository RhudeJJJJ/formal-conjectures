/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode129
import Proofs.RadenkovicGutmanD3Long00StagedUNode153
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e129 e153
noncomputable def p196 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step196 : p196=NestedArithmetic.mul p129 p153 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e129) (NestedArithmetic.compile e153)=p196
  rw [h129,h153]
  exact step196.symm
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
