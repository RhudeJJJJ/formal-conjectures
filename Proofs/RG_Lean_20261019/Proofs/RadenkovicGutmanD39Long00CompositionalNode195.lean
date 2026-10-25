/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode194
import Proofs.RadenkovicGutmanD39Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[156],[0]],[[0,0],[0]],[[2340,0],[0]],[[0,0],[0]],[[14664,0],[0]],[[0,0],[0]],[[49764,0],[0]],[[0,0],[0]],[[99216,0],[0]],[[0,0],[0]],[[118092,78],[78]],[[0,0],[0]],[[81432,546],[546]],[[0,0],[0]],[[29484,1248],[1248]],[[0,0],[0]],[[4212,1014],[1014]],[[0,0],[0]],[[0,234],[234]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
