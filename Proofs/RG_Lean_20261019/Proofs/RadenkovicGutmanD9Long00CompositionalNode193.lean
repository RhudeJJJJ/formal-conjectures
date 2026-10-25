/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode192
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[39,0],[0,0]],[[0,0],[0,0]],[[323,0],[0,0]],[[0,0],[0,0]],[[1484,0],[0,0]],[[0,0],[0,0]],[[4143,0],[0,0]],[[0,0],[0,0]],[[7236,2],[2,0]],[[0,0],[0,0]],[[7832,25],[25,0]],[[0,0],[0,0]],[[4960,116],[116,0]],[[0,0],[0,0]],[[1509,246],[246,0]],[[0,0],[0,0]],[[9,234],[234,0]],[[0,0],[0,0]],[[-81,81],[81,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
