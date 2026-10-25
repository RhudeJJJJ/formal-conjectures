/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode197
import Proofs.RadenkovicGutmanD15Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[105,0],[0,0]],[[0,0],[0,0]],[[1313,0],[0,0]],[[0,0],[0,0]],[[7688,0],[0,0]],[[0,0],[0,0]],[[25197,0],[0,0]],[[0,0],[0,0]],[[49212,2],[2,0]],[[0,0],[0,0]],[[57788,61],[61,0]],[[0,0],[0,0]],[[39364,374],[374,0]],[[0,0],[0,0]],[[13851,858],[858,0]],[[0,0],[0,0]],[[1647,768],[768,0]],[[0,0],[0,0]],[[-135,225],[225,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
