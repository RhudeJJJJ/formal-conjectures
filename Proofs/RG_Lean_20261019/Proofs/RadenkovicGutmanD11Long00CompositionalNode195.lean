/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode194
import Proofs.RadenkovicGutmanD11Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[660,0],[0]],[[0,0],[0]],[[4136,0],[0]],[[0,0],[0]],[[14036,0],[0]],[[0,0],[0]],[[27984,0],[0]],[[0,0],[0]],[[33308,22],[22]],[[0,0],[0]],[[22968,154],[154]],[[0,0],[0]],[[8316,352],[352]],[[0,0],[0]],[[1188,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
