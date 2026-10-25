/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode044
import Proofs.RadenkovicGutmanD12Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0,0]],[[108,108],[108,2]],[[0,0],[0]],[[1926,306],[306]],[[0,0],[0]],[[8682,312],[312]],[[0,0],[0]],[[18554,140],[140]],[[0,0],[0]],[[22588,28],[28]],[[0,0],[0]],[[16920,2],[2]],[[0]],[[8044]],[[0]],[[2426]],[[0]],[[448]],[[0]],[[46]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
