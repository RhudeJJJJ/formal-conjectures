/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode197
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[125,0],[0,0]],[[0,0],[0,0]],[[1613,0],[0,0]],[[0,0],[0,0]],[[9568,0],[0,0]],[[0,0],[0,0]],[[31577,0],[0,0]],[[0,0],[0,0]],[[61932,2],[2,0]],[[0,0],[0,0]],[[72924,73],[73,0]],[[0,0],[0,0]],[[49772,462],[462,0]],[[0,0],[0,0]],[[17543,1074],[1074,0]],[[0,0],[0,0]],[[2091,968],[968,0]],[[0,0],[0,0]],[[-171,285],[285,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
