/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode192
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[74,0],[0,0]],[[0,0],[0,0]],[[848,0],[0,0]],[[0,0],[0,0]],[[4774,0],[0,0]],[[0,0],[0,0]],[[15308,0],[0,0]],[[0,0],[0,0]],[[29496,2],[2,0]],[[0,0],[0,0]],[[34292,60],[60,0]],[[0,0],[0,0]],[[22950,396],[396,0]],[[0,0],[0,0]],[[7354,1016],[1016,0]],[[0,0],[0,0]],[[114,1074],[1074,0]],[[0,0],[0,0]],[[-396,396],[396,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
