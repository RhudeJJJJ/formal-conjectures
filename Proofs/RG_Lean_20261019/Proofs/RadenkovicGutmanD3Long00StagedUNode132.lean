/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode131
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e132 : NestedArithmetic.Expr 3 := .times e131 e120
noncomputable def p132 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step132 : p132=NestedArithmetic.mul p131 p120 := by decide +kernel
#print axioms step132
theorem h132 : NestedArithmetic.compile e132=p132 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e131) (NestedArithmetic.compile e120)=p132
  rw [h131,h120]
  exact step132.symm
#print axioms h132
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
