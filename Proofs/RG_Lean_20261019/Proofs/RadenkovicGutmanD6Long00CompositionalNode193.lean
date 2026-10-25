/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode192
import Proofs.RadenkovicGutmanD6Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[36,0],[0,0]],[[0,0],[0,0]],[[278,0],[0,0]],[[0,0],[0,0]],[[1202,0],[0,0]],[[0,0],[0,0]],[[3186,0],[0,0]],[[0,0],[0,0]],[[5328,2],[2,0]],[[0,0],[0,0]],[[5564,22],[22,0]],[[0,0],[0,0]],[[3418,92],[92,0]],[[0,0],[0,0]],[[1008,180],[180,0]],[[0,0],[0,0]],[[0,162],[162,0]],[[0,0],[0,0]],[[-54,54],[54,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
