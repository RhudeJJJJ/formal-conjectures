/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode171
import Proofs.RadenkovicGutmanD7Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[14,0],[0]],[[0,0],[0]],[[210,0],[0]],[[0,0],[0]],[[1316,0],[0]],[[0,0],[0]],[[4466,0],[0]],[[0,0],[0]],[[8904,0],[0]],[[0,0],[0]],[[10598,7],[7]],[[0,0],[0]],[[7308,49],[49]],[[0,0],[0]],[[2646,112],[112]],[[0,0],[0]],[[378,91],[91]],[[0,0],[0]],[[0,21],[21]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
