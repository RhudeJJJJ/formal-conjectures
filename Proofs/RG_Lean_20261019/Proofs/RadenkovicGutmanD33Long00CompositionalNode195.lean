/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode194
import Proofs.RadenkovicGutmanD33Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[132],[0]],[[0,0],[0]],[[1980,0],[0]],[[0,0],[0]],[[12408,0],[0]],[[0,0],[0]],[[42108,0],[0]],[[0,0],[0]],[[83952,0],[0]],[[0,0],[0]],[[99924,66],[66]],[[0,0],[0]],[[68904,462],[462]],[[0,0],[0]],[[24948,1056],[1056]],[[0,0],[0]],[[3564,858],[858]],[[0,0],[0]],[[0,198],[198]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
