/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode194
import Proofs.RadenkovicGutmanD40Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[160],[0]],[[0,0],[0]],[[2400,0],[0]],[[0,0],[0]],[[15040,0],[0]],[[0,0],[0]],[[51040,0],[0]],[[0,0],[0]],[[101760,0],[0]],[[0,0],[0]],[[121120,80],[80]],[[0,0],[0]],[[83520,560],[560]],[[0,0],[0]],[[30240,1280],[1280]],[[0,0],[0]],[[4320,1040],[1040]],[[0,0],[0]],[[0,240],[240]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
