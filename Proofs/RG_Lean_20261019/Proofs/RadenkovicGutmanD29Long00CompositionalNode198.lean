/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode197
import Proofs.RadenkovicGutmanD29Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[175,0],[0,0]],[[0,0],[0,0]],[[2363,0],[0,0]],[[0,0],[0,0]],[[14268,0],[0,0]],[[0,0],[0,0]],[[47527,0],[0,0]],[[0,0],[0,0]],[[93732,2],[2,0]],[[0,0],[0,0]],[[110764,103],[103,0]],[[0,0],[0,0]],[[75792,682],[682,0]],[[0,0],[0,0]],[[26773,1614],[1614,0]],[[0,0],[0,0]],[[3201,1468],[1468,0]],[[0,0],[0,0]],[[-261,435],[435,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
