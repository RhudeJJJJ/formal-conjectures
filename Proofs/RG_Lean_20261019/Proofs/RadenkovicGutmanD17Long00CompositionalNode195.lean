/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode194
import Proofs.RadenkovicGutmanD17Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[68],[0]],[[0,0],[0]],[[1020,0],[0]],[[0,0],[0]],[[6392,0],[0]],[[0,0],[0]],[[21692,0],[0]],[[0,0],[0]],[[43248,0],[0]],[[0,0],[0]],[[51476,34],[34]],[[0,0],[0]],[[35496,238],[238]],[[0,0],[0]],[[12852,544],[544]],[[0,0],[0]],[[1836,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
