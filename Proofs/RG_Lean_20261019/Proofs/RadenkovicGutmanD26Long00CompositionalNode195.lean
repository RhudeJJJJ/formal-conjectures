/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode194
import Proofs.RadenkovicGutmanD26Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[104],[0]],[[0,0],[0]],[[1560,0],[0]],[[0,0],[0]],[[9776,0],[0]],[[0,0],[0]],[[33176,0],[0]],[[0,0],[0]],[[66144,0],[0]],[[0,0],[0]],[[78728,52],[52]],[[0,0],[0]],[[54288,364],[364]],[[0,0],[0]],[[19656,832],[832]],[[0,0],[0]],[[2808,676],[676]],[[0,0],[0]],[[0,156],[156]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
