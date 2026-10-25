/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode194
import Proofs.RadenkovicGutmanD21Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[84],[0]],[[0,0],[0]],[[1260,0],[0]],[[0,0],[0]],[[7896,0],[0]],[[0,0],[0]],[[26796,0],[0]],[[0,0],[0]],[[53424,0],[0]],[[0,0],[0]],[[63588,42],[42]],[[0,0],[0]],[[43848,294],[294]],[[0,0],[0]],[[15876,672],[672]],[[0,0],[0]],[[2268,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
