/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode197
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[110,0],[0,0]],[[0,0],[0,0]],[[1388,0],[0,0]],[[0,0],[0,0]],[[8158,0],[0,0]],[[0,0],[0,0]],[[26792,0],[0,0]],[[0,0],[0,0]],[[52392,2],[2,0]],[[0,0],[0,0]],[[61572,64],[64,0]],[[0,0],[0,0]],[[41966,396],[396,0]],[[0,0],[0,0]],[[14774,912],[912,0]],[[0,0],[0,0]],[[1758,818],[818,0]],[[0,0],[0,0]],[[-144,240],[240,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
