/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode197
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[210,0],[0,0]],[[0,0],[0,0]],[[2888,0],[0,0]],[[0,0],[0,0]],[[17558,0],[0,0]],[[0,0],[0,0]],[[58692,0],[0,0]],[[0,0],[0,0]],[[115992,2],[2,0]],[[0,0],[0,0]],[[137252,124],[124,0]],[[0,0],[0,0]],[[94006,836],[836,0]],[[0,0],[0,0]],[[33234,1992],[1992,0]],[[0,0],[0,0]],[[3978,1818],[1818,0]],[[0,0],[0,0]],[[-324,540],[540,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
