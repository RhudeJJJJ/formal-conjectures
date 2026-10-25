/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode197
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[788,0],[0,0]],[[0,0],[0,0]],[[4398,0],[0,0]],[[0,0],[0,0]],[[14032,0],[0,0]],[[0,0],[0,0]],[[26952,2],[2,0]],[[0,0],[0,0]],[[31300,40],[40,0]],[[0,0],[0,0]],[[21150,220],[220,0]],[[0,0],[0,0]],[[7390,480],[480,0]],[[0,0],[0,0]],[[870,418],[418,0]],[[0,0],[0,0]],[[-72,120],[120,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
