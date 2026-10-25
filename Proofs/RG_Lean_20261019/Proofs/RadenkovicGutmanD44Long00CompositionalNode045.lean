/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode044
import Proofs.RadenkovicGutmanD44Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0,0]],[[-396,396],[396,2]],[[0,0],[0]],[[114,1074],[1074]],[[0,0],[0]],[[7354,1016],[1016]],[[0,0],[0]],[[22950,396],[396]],[[0,0],[0]],[[34292,60],[60]],[[0,0],[0]],[[29496,2],[2]],[[0]],[[15308]],[[0]],[[4774]],[[0]],[[848]],[[0]],[[74]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
