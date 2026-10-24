/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode142
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e143 : NestedArithmetic.Expr 3 := .times e142 e120
noncomputable def p143 : NestedHorner.Poly 3 := [[[1]],[[0]],[[8]],[[0]],[[22]],[[0]],[[24]],[[0]],[[9]]]
theorem step143 : p143=NestedArithmetic.mul p142 p120 := by decide +kernel
#print axioms step143
theorem h143 : NestedArithmetic.compile e143=p143 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e142) (NestedArithmetic.compile e120)=p143
  rw [h142,h120]
  exact step143.symm
#print axioms h143
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
