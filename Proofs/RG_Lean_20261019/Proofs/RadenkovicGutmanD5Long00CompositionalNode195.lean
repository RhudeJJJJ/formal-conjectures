/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode194
import Proofs.RadenkovicGutmanD5Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[20],[0]],[[0,0],[0]],[[300,0],[0]],[[0,0],[0]],[[1880,0],[0]],[[0,0],[0]],[[6380,0],[0]],[[0,0],[0]],[[12720,0],[0]],[[0,0],[0]],[[15140,10],[10]],[[0,0],[0]],[[10440,70],[70]],[[0,0],[0]],[[3780,160],[160]],[[0,0],[0]],[[540,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
