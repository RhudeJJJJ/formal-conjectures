/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode065
import Proofs.RadenkovicGutmanD7Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[7],[0]],[[0,0],[0]],[[112,0],[0]],[[0,0],[0]],[[749,0],[0]],[[0,0],[0]],[[2716,0],[0]],[[0,0],[0]],[[5796,0],[0]],[[0,0],[0]],[[7392,7],[7]],[[0,0],[0]],[[5453,49],[49]],[[0,0],[0]],[[2100,112],[112]],[[0,0],[0]],[[315,91],[91]],[[0,0],[0]],[[0,21],[21]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
