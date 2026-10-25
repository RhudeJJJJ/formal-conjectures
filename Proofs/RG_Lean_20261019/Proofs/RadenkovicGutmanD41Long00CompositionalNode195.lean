/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode194
import Proofs.RadenkovicGutmanD41Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[164],[0]],[[0,0],[0]],[[2460,0],[0]],[[0,0],[0]],[[15416,0],[0]],[[0,0],[0]],[[52316,0],[0]],[[0,0],[0]],[[104304,0],[0]],[[0,0],[0]],[[124148,82],[82]],[[0,0],[0]],[[85608,574],[574]],[[0,0],[0]],[[30996,1312],[1312]],[[0,0],[0]],[[4428,1066],[1066]],[[0,0],[0]],[[0,246],[246]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
