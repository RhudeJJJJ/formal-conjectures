/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode191
import Proofs.RadenkovicGutmanD44Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[74,0],[0,0]],[[0,0],[0,0]],[[848,0],[0,0]],[[0,0],[0,0]],[[4774,0],[0,0]],[[0,0],[0,0]],[[15308,0],[0,0]],[[0,0],[0,0]],[[29496,2],[2,0]],[[0,0],[0,0]],[[34292,60],[60,0]],[[0,0],[0,0]],[[22950,396],[396,0]],[[0,0],[0,0]],[[7354,1016],[1016,0]],[[0,0],[0,0]],[[114,1074],[1074,0]],[[0,0],[0,0]],[[-396,396],[396,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
