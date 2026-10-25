/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode194
import Proofs.RadenkovicGutmanD18Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[72],[0]],[[0,0],[0]],[[1080,0],[0]],[[0,0],[0]],[[6768,0],[0]],[[0,0],[0]],[[22968,0],[0]],[[0,0],[0]],[[45792,0],[0]],[[0,0],[0]],[[54504,36],[36]],[[0,0],[0]],[[37584,252],[252]],[[0,0],[0]],[[13608,576],[576]],[[0,0],[0]],[[1944,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
