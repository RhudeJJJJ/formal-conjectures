/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode194
import Proofs.RadenkovicGutmanD34Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[136],[0]],[[0,0],[0]],[[2040,0],[0]],[[0,0],[0]],[[12784,0],[0]],[[0,0],[0]],[[43384,0],[0]],[[0,0],[0]],[[86496,0],[0]],[[0,0],[0]],[[102952,68],[68]],[[0,0],[0]],[[70992,476],[476]],[[0,0],[0]],[[25704,1088],[1088]],[[0,0],[0]],[[3672,884],[884]],[[0,0],[0]],[[0,204],[204]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
