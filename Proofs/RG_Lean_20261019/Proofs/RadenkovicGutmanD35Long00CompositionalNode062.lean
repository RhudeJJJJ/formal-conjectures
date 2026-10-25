/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode044
import Proofs.RadenkovicGutmanD35Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0,0]],[[315,315],[315,2]],[[0,0],[0]],[[5583,858],[858]],[[0,0],[0]],[[24713,818],[818]],[[0,0],[0]],[[51444,324],[324]],[[0,0],[0]],[[60400,51],[51]],[[0,0],[0]],[[43048,2],[2]],[[0]],[[19107]],[[0]],[[5232]],[[0]],[[839]],[[0]],[[69]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
