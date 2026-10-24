/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode164
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e120
noncomputable def p165 : NestedHorner.Poly 3 := [[[1],[]],[[0],[0]],[[15],[0]],[[0],[0]],[[94],[0]],[[0],[0]],[[319],[0]],[[0],[0]],[[636],[0]],[[0],[0]],[[757],[1]],[[0],[0]],[[522],[7]],[[0],[0]],[[189],[16]],[[0],[0]],[[27],[13]],[[],[0]],[[],[3]]]
theorem step165 : p165=NestedArithmetic.mul p164 p120 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e164) (NestedArithmetic.compile e120)=p165
  rw [h164,h120]
  exact step165.symm
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
