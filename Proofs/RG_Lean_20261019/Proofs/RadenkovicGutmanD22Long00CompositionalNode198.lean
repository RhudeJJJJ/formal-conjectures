/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode197
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[140,0],[0,0]],[[0,0],[0,0]],[[1838,0],[0,0]],[[0,0],[0,0]],[[10978,0],[0,0]],[[0,0],[0,0]],[[36362,0],[0,0]],[[0,0],[0,0]],[[71472,2],[2,0]],[[0,0],[0,0]],[[84276,82],[82,0]],[[0,0],[0,0]],[[57578,528],[528,0]],[[0,0],[0,0]],[[20312,1236],[1236,0]],[[0,0],[0,0]],[[2424,1118],[1118,0]],[[0,0],[0,0]],[[-198,330],[330,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
