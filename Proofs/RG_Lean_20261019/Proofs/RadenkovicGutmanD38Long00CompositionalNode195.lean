/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode194
import Proofs.RadenkovicGutmanD38Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[152],[0]],[[0,0],[0]],[[2280,0],[0]],[[0,0],[0]],[[14288,0],[0]],[[0,0],[0]],[[48488,0],[0]],[[0,0],[0]],[[96672,0],[0]],[[0,0],[0]],[[115064,76],[76]],[[0,0],[0]],[[79344,532],[532]],[[0,0],[0]],[[28728,1216],[1216]],[[0,0],[0]],[[4104,988],[988]],[[0,0],[0]],[[0,228],[228]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
