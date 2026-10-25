/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode192
import Proofs.RadenkovicGutmanD26Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[56,0],[0,0]],[[0,0],[0,0]],[[578,0],[0,0]],[[0,0],[0,0]],[[3082,0],[0,0]],[[0,0],[0,0]],[[9566,0],[0,0]],[[0,0],[0,0]],[[18048,2],[2,0]],[[0,0],[0,0]],[[20684,42],[42,0]],[[0,0],[0,0]],[[13698,252],[252,0]],[[0,0],[0,0]],[[4348,620],[620,0]],[[0,0],[0,0]],[[60,642],[642,0]],[[0,0],[0,0]],[[-234,234],[234,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
