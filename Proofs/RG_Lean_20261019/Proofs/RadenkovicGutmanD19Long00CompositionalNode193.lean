/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode192
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[49,0],[0,0]],[[0,0],[0,0]],[[473,0],[0,0]],[[0,0],[0,0]],[[2424,0],[0,0]],[[0,0],[0,0]],[[7333,0],[0,0]],[[0,0],[0,0]],[[13596,2],[2,0]],[[0,0],[0,0]],[[15392,35],[35,0]],[[0,0],[0,0]],[[10100,196],[196,0]],[[0,0],[0,0]],[[3179,466],[466,0]],[[0,0],[0,0]],[[39,474],[474,0]],[[0,0],[0,0]],[[-171,171],[171,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
