/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode191
import Proofs.RadenkovicGutmanD35Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[69,0],[0,0]],[[0,0],[0,0]],[[839,0],[0,0]],[[0,0],[0,0]],[[5232,0],[0,0]],[[0,0],[0,0]],[[19107,0],[0,0]],[[0,0],[0,0]],[[43048,2],[2,0]],[[0,0],[0,0]],[[60400,51],[51,0]],[[0,0],[0,0]],[[51444,324],[324,0]],[[0,0],[0,0]],[[24713,818],[818,0]],[[0,0],[0,0]],[[5583,858],[858,0]],[[0,0],[0,0]],[[315,315],[315,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
