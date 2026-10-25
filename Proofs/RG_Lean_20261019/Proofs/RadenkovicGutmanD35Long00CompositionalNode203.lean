/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode202
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[69,0],[0,0]],[[0,0],[0,0]],[[839,0],[0,0]],[[0,0],[0,0]],[[5232,0],[0,0]],[[0,0],[0,0]],[[19107,0],[0,0]],[[0,0],[0,0]],[[43048,2],[2,0]],[[0,0],[0,0]],[[60400,51],[51,0]],[[0,0],[0,0]],[[51444,324],[324,0]],[[0,0],[0,0]],[[24713,818],[818,0]],[[0,0],[0,0]],[[5583,858],[858,0]],[[0,0],[0,0]],[[315,315],[315,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
