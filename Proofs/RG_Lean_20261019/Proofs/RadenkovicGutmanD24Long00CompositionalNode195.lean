/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode194
import Proofs.RadenkovicGutmanD24Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[96],[0]],[[0,0],[0]],[[1440,0],[0]],[[0,0],[0]],[[9024,0],[0]],[[0,0],[0]],[[30624,0],[0]],[[0,0],[0]],[[61056,0],[0]],[[0,0],[0]],[[72672,48],[48]],[[0,0],[0]],[[50112,336],[336]],[[0,0],[0]],[[18144,768],[768]],[[0,0],[0]],[[2592,624],[624]],[[0,0],[0]],[[0,144],[144]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
