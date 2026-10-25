/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode044
import Proofs.RadenkovicGutmanD32Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0,0]],[[288,288],[288,2]],[[0,0],[0]],[[5106,786],[786]],[[0,0],[0]],[[22622,752],[752]],[[0,0],[0]],[[47154,300],[300]],[[0,0],[0]],[[55468,48],[48]],[[0,0],[0]],[[39640,2],[2]],[[0]],[[17664]],[[0]],[[4866]],[[0]],[[788]],[[0]],[[66]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
