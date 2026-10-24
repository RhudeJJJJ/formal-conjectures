/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode166
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e167 : NestedArithmetic.Expr 3 := .times e166 e120
noncomputable def p167 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[15,0]],[[0,0]],[[94,0]],[[0,0]],[[319,0]],[[0,0]],[[636,0]],[[0,0]],[[757,1]],[[0,0]],[[522,7]],[[0,0]],[[189,16]],[[0,0]],[[27,13]],[[0,0]],[[0,3]]]
theorem step167 : p167=NestedArithmetic.mul p166 p120 := by decide +kernel
#print axioms step167
theorem h167 : NestedArithmetic.compile e167=p167 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e166) (NestedArithmetic.compile e120)=p167
  rw [h166,h120]
  exact step167.symm
#print axioms h167
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
