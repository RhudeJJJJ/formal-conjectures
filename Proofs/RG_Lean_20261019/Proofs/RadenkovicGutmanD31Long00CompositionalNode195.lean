/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode194
import Proofs.RadenkovicGutmanD31Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[124],[0]],[[0,0],[0]],[[1860,0],[0]],[[0,0],[0]],[[11656,0],[0]],[[0,0],[0]],[[39556,0],[0]],[[0,0],[0]],[[78864,0],[0]],[[0,0],[0]],[[93868,62],[62]],[[0,0],[0]],[[64728,434],[434]],[[0,0],[0]],[[23436,992],[992]],[[0,0],[0]],[[3348,806],[806]],[[0,0],[0]],[[0,186],[186]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
