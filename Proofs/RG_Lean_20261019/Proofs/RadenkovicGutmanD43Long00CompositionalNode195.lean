/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode194
import Proofs.RadenkovicGutmanD43Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[172],[0]],[[0,0],[0]],[[2580,0],[0]],[[0,0],[0]],[[16168,0],[0]],[[0,0],[0]],[[54868,0],[0]],[[0,0],[0]],[[109392,0],[0]],[[0,0],[0]],[[130204,86],[86]],[[0,0],[0]],[[89784,602],[602]],[[0,0],[0]],[[32508,1376],[1376]],[[0,0],[0]],[[4644,1118],[1118]],[[0,0],[0]],[[0,258],[258]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
