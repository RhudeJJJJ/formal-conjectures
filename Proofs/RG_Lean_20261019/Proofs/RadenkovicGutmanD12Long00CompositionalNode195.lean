/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode194
import Proofs.RadenkovicGutmanD12Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[48],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4512,0],[0]],[[0,0],[0]],[[15312,0],[0]],[[0,0],[0]],[[30528,0],[0]],[[0,0],[0]],[[36336,24],[24]],[[0,0],[0]],[[25056,168],[168]],[[0,0],[0]],[[9072,384],[384]],[[0,0],[0]],[[1296,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
