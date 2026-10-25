/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode197
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[220,0],[0,0]],[[0,0],[0,0]],[[3038,0],[0,0]],[[0,0],[0,0]],[[18498,0],[0,0]],[[0,0],[0,0]],[[61882,0],[0,0]],[[0,0],[0,0]],[[122352,2],[2,0]],[[0,0],[0,0]],[[144820,130],[130,0]],[[0,0],[0,0]],[[99210,880],[880,0]],[[0,0],[0,0]],[[35080,2100],[2100,0]],[[0,0],[0,0]],[[4200,1918],[1918,0]],[[0,0],[0,0]],[[-342,570],[570,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
