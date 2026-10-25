/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode197
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[85,0],[0,0]],[[0,0],[0,0]],[[1013,0],[0,0]],[[0,0],[0,0]],[[5808,0],[0,0]],[[0,0],[0,0]],[[18817,0],[0,0]],[[0,0],[0,0]],[[36492,2],[2,0]],[[0,0],[0,0]],[[42652,49],[49,0]],[[0,0],[0,0]],[[28956,286],[286,0]],[[0,0],[0,0]],[[10159,642],[642,0]],[[0,0],[0,0]],[[1203,568],[568,0]],[[0,0],[0,0]],[[-99,165],[165,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
