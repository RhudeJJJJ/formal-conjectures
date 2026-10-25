/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode030
import Proofs.RadenkovicGutmanD7Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[7],[0]],[[0,0],[0]],[[112,0],[0]],[[0,0],[0]],[[749,0],[0]],[[0,0],[0]],[[2716,0],[0]],[[0,0],[0]],[[5796,0],[0]],[[0,0],[0]],[[7392,7],[7]],[[0,0],[0]],[[5453,49],[49]],[[0,0],[0]],[[2100,112],[112]],[[0,0],[0]],[[315,91],[91]],[[0,0],[0]],[[0,21],[21]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
