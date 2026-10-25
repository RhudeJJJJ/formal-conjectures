/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode194
import Proofs.RadenkovicGutmanD14Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[56],[0]],[[0,0],[0]],[[840,0],[0]],[[0,0],[0]],[[5264,0],[0]],[[0,0],[0]],[[17864,0],[0]],[[0,0],[0]],[[35616,0],[0]],[[0,0],[0]],[[42392,28],[28]],[[0,0],[0]],[[29232,196],[196]],[[0,0],[0]],[[10584,448],[448]],[[0,0],[0]],[[1512,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
