/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode191
import Proofs.RadenkovicGutmanD19Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[49,0],[0,0]],[[0,0],[0,0]],[[473,0],[0,0]],[[0,0],[0,0]],[[2424,0],[0,0]],[[0,0],[0,0]],[[7333,0],[0,0]],[[0,0],[0,0]],[[13596,2],[2,0]],[[0,0],[0,0]],[[15392,35],[35,0]],[[0,0],[0,0]],[[10100,196],[196,0]],[[0,0],[0,0]],[[3179,466],[466,0]],[[0,0],[0,0]],[[39,474],[474,0]],[[0,0],[0,0]],[[-171,171],[171,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
