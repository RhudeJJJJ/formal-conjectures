/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode025
import Proofs.RadenkovicGutmanD3Long00StagedUNode144
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e147 : NestedArithmetic.Expr 3 := .times e025 e144
noncomputable def p147 : NestedHorner.Poly 3 := [[[]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,0]],[[0,1]]]
theorem step147 : p147=NestedArithmetic.mul p025 p144 := by decide +kernel
#print axioms step147
theorem h147 : NestedArithmetic.compile e147=p147 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e025) (NestedArithmetic.compile e144)=p147
  rw [h025,h144]
  exact step147.symm
#print axioms h147
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
