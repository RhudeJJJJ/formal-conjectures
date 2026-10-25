/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode030
import Proofs.RadenkovicGutmanD7Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[210,0],[0]],[[0,0],[0]],[[1316,0],[0]],[[0,0],[0]],[[4466,0],[0]],[[0,0],[0]],[[8904,0],[0]],[[0,0],[0]],[[10598,7],[7]],[[0,0],[0]],[[7308,49],[49]],[[0,0],[0]],[[2646,112],[112]],[[0,0],[0]],[[378,91],[91]],[[0,0],[0]],[[0,21],[21]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
