/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode195
import Proofs.RadenkovicGutmanD2Long00CompositionalNode197
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .plus e195 e197
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[44,0],[0,0]],[[0,0],[0,0]],[[394,0],[0,0]],[[0,0],[0,0]],[[1902,0],[0,0]],[[0,0],[0,0]],[[5462,0],[0,0]],[[0,0],[0,0]],[[9648,2],[2,0]],[[0,0],[0,0]],[[10428,22],[22,0]],[[0,0],[0,0]],[[6598,88],[88,0]],[[0,0],[0,0]],[[2164,156],[156,0]],[[0,0],[0,0]],[[240,118],[118,0]],[[0,0],[0,0]],[[-18,30],[30,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step198 : p198=NestedHorner.add p195 p197 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_plus e198 e195 e197 p195 p197 p198 rfl h195 h197 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
