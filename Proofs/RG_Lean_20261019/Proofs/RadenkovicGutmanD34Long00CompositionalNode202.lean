/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode191
import Proofs.RadenkovicGutmanD34Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[68,0],[0,0]],[[0,0],[0,0]],[[822,0],[0,0]],[[0,0],[0,0]],[[5110,0],[0,0]],[[0,0],[0,0]],[[18626,0],[0,0]],[[0,0],[0,0]],[[41912,2],[2,0]],[[0,0],[0,0]],[[58756,50],[50,0]],[[0,0],[0,0]],[[50014,316],[316,0]],[[0,0],[0,0]],[[24016,796],[796,0]],[[0,0],[0,0]],[[5424,834],[834,0]],[[0,0],[0,0]],[[306,306],[306,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
