/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode009
import Proofs.RadenkovicGutmanD3Long00StagedUNode153
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e009 e153
noncomputable def p159 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step159 : p159=NestedArithmetic.mul p009 p153 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e009) (NestedArithmetic.compile e153)=p159
  rw [h009,h153]
  exact step159.symm
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
