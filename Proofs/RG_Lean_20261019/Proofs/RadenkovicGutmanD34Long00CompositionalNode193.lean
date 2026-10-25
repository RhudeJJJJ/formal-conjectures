/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode192
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[698,0],[0,0]],[[0,0],[0,0]],[[3834,0],[0,0]],[[0,0],[0,0]],[[12118,0],[0,0]],[[0,0],[0,0]],[[23136,2],[2,0]],[[0,0],[0,0]],[[26732,50],[50,0]],[[0,0],[0,0]],[[17810,316],[316,0]],[[0,0],[0,0]],[[5684,796],[796,0]],[[0,0],[0,0]],[[84,834],[834,0]],[[0,0],[0,0]],[[-306,306],[306,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
