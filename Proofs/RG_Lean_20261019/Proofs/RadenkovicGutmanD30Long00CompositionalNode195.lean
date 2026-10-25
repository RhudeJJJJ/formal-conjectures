/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode194
import Proofs.RadenkovicGutmanD30Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[120],[0]],[[0,0],[0]],[[1800,0],[0]],[[0,0],[0]],[[11280,0],[0]],[[0,0],[0]],[[38280,0],[0]],[[0,0],[0]],[[76320,0],[0]],[[0,0],[0]],[[90840,60],[60]],[[0,0],[0]],[[62640,420],[420]],[[0,0],[0]],[[22680,960],[960]],[[0,0],[0]],[[3240,780],[780]],[[0,0],[0]],[[0,180],[180]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
