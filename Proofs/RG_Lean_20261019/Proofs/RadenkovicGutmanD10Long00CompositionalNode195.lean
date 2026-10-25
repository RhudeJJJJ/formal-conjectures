/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode194
import Proofs.RadenkovicGutmanD10Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[40],[0]],[[0,0],[0]],[[600,0],[0]],[[0,0],[0]],[[3760,0],[0]],[[0,0],[0]],[[12760,0],[0]],[[0,0],[0]],[[25440,0],[0]],[[0,0],[0]],[[30280,20],[20]],[[0,0],[0]],[[20880,140],[140]],[[0,0],[0]],[[7560,320],[320]],[[0,0],[0]],[[1080,260],[260]],[[0,0],[0]],[[0,60],[60]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
