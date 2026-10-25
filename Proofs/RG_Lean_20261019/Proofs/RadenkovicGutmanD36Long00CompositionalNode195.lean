/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode194
import Proofs.RadenkovicGutmanD36Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[144],[0]],[[0,0],[0]],[[2160,0],[0]],[[0,0],[0]],[[13536,0],[0]],[[0,0],[0]],[[45936,0],[0]],[[0,0],[0]],[[91584,0],[0]],[[0,0],[0]],[[109008,72],[72]],[[0,0],[0]],[[75168,504],[504]],[[0,0],[0]],[[27216,1152],[1152]],[[0,0],[0]],[[3888,936],[936]],[[0,0],[0]],[[0,216],[216]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
