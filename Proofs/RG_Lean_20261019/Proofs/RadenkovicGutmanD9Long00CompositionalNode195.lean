/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode194
import Proofs.RadenkovicGutmanD9Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[540,0],[0]],[[0,0],[0]],[[3384,0],[0]],[[0,0],[0]],[[11484,0],[0]],[[0,0],[0]],[[22896,0],[0]],[[0,0],[0]],[[27252,18],[18]],[[0,0],[0]],[[18792,126],[126]],[[0,0],[0]],[[6804,288],[288]],[[0,0],[0]],[[972,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
