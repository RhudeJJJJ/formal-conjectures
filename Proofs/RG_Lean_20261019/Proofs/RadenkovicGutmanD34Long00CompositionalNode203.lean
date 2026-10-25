/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode202
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[68,0],[0,0]],[[0,0],[0,0]],[[822,0],[0,0]],[[0,0],[0,0]],[[5110,0],[0,0]],[[0,0],[0,0]],[[18626,0],[0,0]],[[0,0],[0,0]],[[41912,2],[2,0]],[[0,0],[0,0]],[[58756,50],[50,0]],[[0,0],[0,0]],[[50014,316],[316,0]],[[0,0],[0,0]],[[24016,796],[796,0]],[[0,0],[0,0]],[[5424,834],[834,0]],[[0,0],[0,0]],[[306,306],[306,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
