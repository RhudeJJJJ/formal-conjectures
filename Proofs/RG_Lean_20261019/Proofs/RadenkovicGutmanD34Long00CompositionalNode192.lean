/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode191
import Proofs.RadenkovicGutmanD34Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[698,0],[0,0]],[[0,0],[0,0]],[[3834,0],[0,0]],[[0,0],[0,0]],[[12118,0],[0,0]],[[0,0],[0,0]],[[23136,2],[2,0]],[[0,0],[0,0]],[[26732,50],[50,0]],[[0,0],[0,0]],[[17810,316],[316,0]],[[0,0],[0,0]],[[5684,796],[796,0]],[[0,0],[0,0]],[[84,834],[834,0]],[[0,0],[0,0]],[[-306,306],[306,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
